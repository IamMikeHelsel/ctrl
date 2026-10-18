import CutWitness
import Erdos128.BalancedBlowup
import Erdos128.RoundingFinal
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
/-! Exact attributed extraction; see extraction.json. Only import context changes. -/
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Exact degree-two homogeneity of the unnormalized piecewise envelope. -/
theorem completionEnvelope_scale (s a t : ℚ) (hs : 0 < s) :
    completionEnvelope (s * a) (s * t) = s ^ 2 * completionEnvelope a t := by
  have hb : 4 * (s * a) ≤ 3 * (s * t) ↔ 4 * a ≤ 3 * t := by
    rw [show 4 * (s * a) = s * (4 * a) by ring,
      show 3 * (s * t) = s * (3 * t) by ring]
    constructor
    · intro h
      nlinarith
    · exact fun h => mul_le_mul_of_nonneg_left h hs.le
  unfold completionEnvelope
  simp only [hb]
  split_ifs <;> ring

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

end
end Erdos128.CompletionBridge
