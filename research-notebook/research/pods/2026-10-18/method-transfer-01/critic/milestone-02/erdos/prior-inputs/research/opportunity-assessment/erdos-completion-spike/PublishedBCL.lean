import FixedCutBound
import Erdos128.BalancedBlowup
import Erdos128.RoundingFinal
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

/-! The two BCL transport lemmas are extracted from the pinned aimir baseline
BCLCertificate/Bridge.lean, commit ba85f319ebb33ec2194ef4c2929a12916329e1e7.
Only their namespace/import context changes. They are attributed reused proofs.
The new endpoint connects the fully proved completion construction and exact
scalar certificate, then reuses proved blow-up and rounding bridges.
-/
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The external published input, arXiv:2103.14179v1, PDF Theorem 2(a).
It is a transparent proposition consumed as a hypothesis, not an axiom. -/
def BCLEventual : Prop :=
  ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    N ≤ Fintype.card W → H.CliqueFree 3 → BCLCutCertificate H

theorem bclCutCertificate_iff_normalizedInternalCutBoundQ
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    BCLCutCertificate G ↔
      HasNormalizedInternalCutBoundQ G (2 / 47 : ℚ) := by
  have hn : (0 : ℚ) < (Fintype.card V : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hn2 : (0 : ℚ) < (Fintype.card V : ℚ) ^ 2 := sq_pos_of_pos hn
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    unfold normalizedInternalCutCostQ
    exact (div_le_iff₀ hn2).2 hS
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    unfold normalizedInternalCutCostQ at hS
    exact (div_le_iff₀ hn2).1 hS

/-- A BCL theorem valid above some finite order is valid for every nonempty
finite triangle-free graph.

Apply the eventual theorem to a sufficiently large positive balanced blow-up.
The normalized internal-cut bound descends exactly along the blow-up, with no
error term and no compactness or limit axiom. -/
theorem bclCutCertificate_all_of_eventually
    (hEventually : ∃ N : ℕ,
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        N ≤ Fintype.card W → H.CliqueFree 3 → BCLCutCertificate H) :
    ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      H.CliqueFree 3 → BCLCutCertificate H := by
  obtain ⟨N, hlarge⟩ := hEventually
  intro W instFintype instDecidableEq instNonempty H instDecidableAdj htriangle
  let k := N + 1
  have hk : 0 < k := by
    simp [k]
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hcard : N ≤ Fintype.card (W × Fin k) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hW : 0 < Fintype.card W := Fintype.card_pos
    calc
      N ≤ N + 1 := Nat.le_succ N
      _ ≤ Fintype.card W * (N + 1) :=
        Nat.le_mul_of_pos_left (N + 1) hW
      _ = Fintype.card W * k := by rfl
  have hblowTriangle : (balancedBlowup H k).CliqueFree 3 :=
    cliqueFree_balancedBlowup H k hk htriangle
  have hblowCertificate : BCLCutCertificate (balancedBlowup H k) :=
    hlarge (W × Fin k) (balancedBlowup H k) hcard hblowTriangle
  have hblowNormalized :
      HasNormalizedInternalCutBoundQ (balancedBlowup H k) (2 / 47 : ℚ) :=
    (bclCutCertificate_iff_normalizedInternalCutBoundQ
      (balancedBlowup H k)).1 hblowCertificate
  have hnormalized : HasNormalizedInternalCutBoundQ H (2 / 47 : ℚ) :=
    (hasNormalizedInternalCutBoundQ_balancedBlowup_iff
      H k hk (2 / 47 : ℚ)).1 hblowNormalized
  exact (bclCutCertificate_iff_normalizedInternalCutBoundQ H).2 hnormalized

/-- Every finite order, including odd order: apply the proved even-order
construction to the two-fold blow-up, then average each independent twin class.
The only external mathematical input is the precisely stated BCL hypothesis. -/
theorem fractional_2587_100000_all_orders
    (hBCL : BCLEventual.{u}) (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) :
    HasNormalizedFractionalHalfBoundQ G (2587 / 100000 : ℚ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hempty =>
    letI : IsEmpty V := hempty
    refine ⟨fun _ => 0, ⟨by intro v; exact isEmptyElim v, by simp⟩, ?_⟩
    norm_num [normalizedEdgeCostQ, edgeCost, edgeBilin]
  | inr hne =>
    letI : Nonempty V := hne
    have hn : 0 < Fintype.card V := Fintype.card_pos
    let H := balancedBlowup G 2
    have hHtri : H.CliqueFree 3 := cliqueFree_balancedBlowup G 2 (by omega) htri
    have hHcut : BCLCutCertificate H :=
      bclCutCertificate_all_of_eventually hBCL (V × Fin 2) H hHtri
    have hHeven : 2 * Fintype.card V = Fintype.card (V × Fin 2) := by
      simp [Fintype.card_prod, Nat.mul_comm]
    obtain ⟨z, hz, hcost⟩ := sparse_fractional_half_of_bcl_cut_even H hHtri
      (Fintype.card V) hn hHeven (by
        obtain ⟨X, hX⟩ := hHcut
        exact ⟨X, by simpa only [Nat.cast_add] using hX⟩)
    have hHnorm : HasNormalizedFractionalHalfBoundQ H (2587 / 100000 : ℚ) := by
      refine ⟨z, hz, ?_⟩
      unfold normalizedEdgeCostQ
      apply (div_le_iff₀ (sq_pos_of_pos (show (0 : ℚ) < (Fintype.card (V × Fin 2) : ℚ) by
        exact_mod_cast Fintype.card_pos))).mpr
      exact hcost.le
    exact (hasNormalizedFractionalHalfBoundQ_balancedBlowup_iff G 2 (by omega) _).mp hHnorm

/-- All finite graphs, integer floor-half conclusion, conditional only on
BCL in its published asymptotic form. This formalizes the existing proposed
2587/100000 argument; it does not prove the conjectural coefficient 1/50. -/
theorem sparse_half_2587_100000
    (hBCL : ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      N ≤ Fintype.card W → H.CliqueFree 3 → BCLCutCertificate H)
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3) :
    ∃ S : Finset V, S.card = Fintype.card V / 2 ∧
      (edgeCountOn G S : ℚ) ≤ (2587 / 100000 : ℚ) * (Fintype.card V : ℚ) ^ 2 := by
  classical
  change HasSparseHalf G _
  cases isEmpty_or_nonempty V with
  | inl hempty =>
    letI : IsEmpty V := hempty
    exact ⟨∅, by simp, by simp [edgeCountOn]⟩
  | inr hne =>
    letI : Nonempty V := hne
    obtain ⟨z, hz, hcost⟩ := fractional_2587_100000_all_orders hBCL G htri
    apply hasSparseHalf_of_hasFractionalHalfBound G
    refine ⟨z, hz, ?_⟩
    exact (div_le_iff₀ (sq_pos_of_pos (show (0 : ℚ) < (Fintype.card V : ℚ) by
      exact_mod_cast Fintype.card_pos))).mp hcost

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.bclCutCertificate_iff_normalizedInternalCutBoundQ
#print axioms Erdos128.CompletionBridge.bclCutCertificate_all_of_eventually
#print axioms Erdos128.CompletionBridge.fractional_2587_100000_all_orders
#print axioms Erdos128.CompletionBridge.sparse_half_2587_100000
#print Erdos128.CompletionBridge.BCLEventual

#check @Erdos128.CompletionBridge.sparse_half_2587_100000
