import CutScalar
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
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

/-- Conditional global-constant result for a positive even-order graph and
one oriented cut satisfying the quoted BCL cost bound. The cut inequality is
an explicit hypothesis; BCL itself is neither assumed as an axiom nor proved. -/
theorem sparse_fractional_half_of_cut_even
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (X : Finset V) (t : ℕ) (ht : 0 < t) (hhalf : 2 * t = Fintype.card V)
    (hXt : X.card ≤ t)
    (hcut : (edgeCountOn G X : ℚ) + (edgeCountOn G Xᶜ : ℚ) ≤
      SparseHalf.I * (Fintype.card V : ℚ) ^ 2) :
    ∃ z : V → ℚ, IsFractionalHalf z ∧
      edgeCost G z < (2587 / 100000 : ℚ) * (Fintype.card V : ℚ) ^ 2 := by
  classical
  let n : ℚ := Fintype.card V
  let a : ℚ := X.card
  let y : ℚ := Xᶜ.card
  let c : ℚ := (t : ℚ) / y
  let x : ℚ := a / n
  let q : ℚ := (edgeCountOn G X : ℚ) / n ^ 2
  let j : ℚ := (edgeCountOn G Xᶜ : ℚ) / n ^ 2
  have htQ : (0 : ℚ) < (t : ℚ) := by exact_mod_cast ht
  have hn : n = 2 * (t : ℚ) := by dsimp [n]; exact_mod_cast hhalf.symm
  have hnpos : 0 < n := by linarith
  have hn2 : 0 < n ^ 2 := sq_pos_of_pos hnpos
  have hnn : n ≠ 0 := ne_of_gt hnpos
  have hnn2 : n ^ 2 ≠ 0 := ne_of_gt hn2
  have hYcard : Xᶜ.card = 2 * t - X.card := by rw [Finset.card_compl, ← hhalf]
  have htY : t ≤ Xᶜ.card := by omega
  have hY : Xᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hypos : 0 < y := by dsimp [y]; exact_mod_cast hY.card_pos
  have hyn : y ≠ 0 := ne_of_gt hypos
  have hay : a + y = n := by
    dsimp [a, y, n]
    exact_mod_cast Finset.card_add_card_compl X
  have hc : 0 < c := div_pos htQ hypos
  have hcy : c * y = (t : ℚ) := div_mul_cancel₀ _ hyn
  have hax : n * x = a := mul_div_cancel₀ _ hnn
  have hcx : 2 * c * (1 - x) = 1 := by
    dsimp [c, x]
    field_simp [hyn, hnn]
    nlinarith [hay, hn]
  have hq : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) hn2.le
  have hcutN : q + j ≤ SparseHalf.I := by
    change (edgeCountOn G X : ℚ) / n ^ 2 + (edgeCountOn G Xᶜ : ℚ) / n ^ 2 ≤ _
    rw [← add_div]
    exact (div_le_iff₀ hn2).mpr hcut
  have huniform : HasFractionalHalfBound G (c ^ 2 * (edgeCountOn G Xᶜ : ℚ)) :=
    uniform_side_fractional_half G Xᶜ hY t htY hhalf
  have hnormalize_first : (c ^ 2 * (edgeCountOn G Xᶜ : ℚ)) / n ^ 2 = c ^ 2 * j := by
    dsimp [j]
    ring
  by_cases hhigh : SparseHalf.c0 ≤ c
  · have hc34 : (3 / 4 : ℚ) ≤ c := by dsimp [SparseHalf.c0] at hhigh; linarith
    have hc34y := mul_le_mul_of_nonneg_right hc34 hypos.le
    have hthirdQ : 2 * (t : ℚ) ≤ 3 * a := by nlinarith [hay, hn, hcy]
    have hthird : 2 * t ≤ 3 * X.card := by dsimp [a] at hthirdQ; exact_mod_cast hthirdQ
    obtain ⟨z, hz, hcost⟩ := cut_two_witness_bound_even G htri X t ht hhalf hthird hXt
    let raw : ℚ := min (c ^ 2 * (edgeCountOn G Xᶜ : ℚ))
      (completionEnvelope a (t : ℚ) + (edgeCountOn G X : ℚ))
    let beta : ℚ := raw / n ^ 2
    have hfirst : beta ≤ c ^ 2 * j := by
      rw [← hnormalize_first]
      exact div_le_div_of_nonneg_right (min_le_left _ _) hn2.le
    have hscale : completionEnvelope a (t : ℚ) = n ^ 2 * completionEnvelope x (1 / 2) := by
      have hh := completionEnvelope_scale n x (1 / 2) hnpos
      rw [hax, show n * (1 / 2) = (t : ℚ) by linarith] at hh
      exact hh
    have hsecond : beta ≤ completionEnvelope x (1 / 2) + q := by
      have hh := div_le_div_of_nonneg_right (min_le_right
        (c ^ 2 * (edgeCountOn G Xᶜ : ℚ))
        (completionEnvelope a (t : ℚ) + (edgeCountOn G X : ℚ))) hn2.le
      change beta ≤ _ at hh
      rw [add_div, hscale, mul_div_cancel_left₀ _ hnn2] at hh
      exact hh
    have hbeta := cut_scalar_bound c x q j beta hc hcx hq hcutN hfirst (fun _ => hsecond)
    have hraw : raw < SparseHalf.T * n ^ 2 := (div_lt_iff₀ hn2).mp hbeta
    refine ⟨z, hz, ?_⟩
    exact hcost.trans_lt hraw
  · obtain ⟨z, hz, hcost⟩ := huniform
    let beta : ℚ := (c ^ 2 * (edgeCountOn G Xᶜ : ℚ)) / n ^ 2
    have hfirst : beta ≤ c ^ 2 * j := hnormalize_first.le
    have hbeta := cut_scalar_bound c x q j beta hc hcx hq hcutN hfirst
      (fun h => (hhigh h).elim)
    have hraw : c ^ 2 * (edgeCountOn G Xᶜ : ℚ) < SparseHalf.T * n ^ 2 :=
      (div_lt_iff₀ hn2).mp hbeta
    exact ⟨z, hz, hcost.trans_lt hraw⟩

/-- A fixed-graph BCL cut input suffices; the orientation of its sides is
chosen inside the proof. Still an even-order fractional statement. -/
theorem sparse_fractional_half_of_bcl_cut_even
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (t : ℕ) (ht : 0 < t) (hhalf : 2 * t = Fintype.card V)
    (hBCL : ∃ X : Finset V,
      (edgeCountOn G X : ℚ) + (edgeCountOn G Xᶜ : ℚ) ≤
        (2 / 47 : ℚ) * (Fintype.card V : ℚ) ^ 2) :
    ∃ z : V → ℚ, IsFractionalHalf z ∧
      edgeCost G z < (2587 / 100000 : ℚ) * (Fintype.card V : ℚ) ^ 2 := by
  obtain ⟨X, hX⟩ := hBCL
  by_cases hXt : X.card ≤ t
  · exact sparse_fractional_half_of_cut_even G htri X t ht hhalf hXt hX
  · have hXct : Xᶜ.card ≤ t := by rw [Finset.card_compl]; omega
    apply sparse_fractional_half_of_cut_even G htri Xᶜ t ht hhalf hXct
    simpa only [compl_compl, add_comm, SparseHalf.I] using hX

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.completionEnvelope_scale
#print axioms Erdos128.CompletionBridge.sparse_fractional_half_of_cut_even
#print axioms Erdos128.CompletionBridge.sparse_fractional_half_of_bcl_cut_even
