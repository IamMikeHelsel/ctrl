import PiecewiseCompletion
set_option maxHeartbeats 1000000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A constant rational weight on a sufficiently large nonempty side is an
actual fractional half; its cost is the exact scaled induced-edge count. -/
theorem uniform_side_fractional_half
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (hY : Y.Nonempty)
    (t : ℕ) (htY : t ≤ Y.card) (hhalf : 2 * t = Fintype.card V) :
    HasFractionalHalfBound G
      (((t : ℚ) / (Y.card : ℚ)) ^ 2 * (edgeCountOn G Y : ℚ)) := by
  let c : ℚ := (t : ℚ) / (Y.card : ℚ)
  have hYpos : (0 : ℚ) < (Y.card : ℚ) := by exact_mod_cast hY.card_pos
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hYpos.le
  have hc1 : c ≤ 1 := (div_le_one hYpos).mpr (by exact_mod_cast htY)
  refine ⟨(fun v => c * finsetIndicator Y v), ⟨?_, ?_⟩, ?_⟩
  · intro v
    by_cases hv : v ∈ Y <;> simp [finsetIndicator, hv, hc0, hc1]
  · rw [← Finset.mul_sum, sum_finsetIndicator]
    have hc : c * (Y.card : ℚ) = (t : ℚ) := div_mul_cancel₀ _ (ne_of_gt hYpos)
    rw [hc]
    have hn : (2 : ℚ) * (t : ℚ) = (Fintype.card V : ℚ) := by exact_mod_cast hhalf
    linarith
  · rw [edgeCost_smul, edgeCost_finsetIndicator]

theorem fractional_bound_min
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : ℚ}
    (ha : HasFractionalHalfBound G a) (hb : HasFractionalHalfBound G b) :
    HasFractionalHalfBound G (min a b) := by
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab] using ha
  · simpa [min_eq_right hba] using hb

/-- Both actual cut constructions are now supplied to the scalar interface.
No max-cut or BCL claim is assumed: the bound holds for any eligible cut. -/
theorem cut_two_witness_bound_even
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (X : Finset V) (t : ℕ) (ht : 0 < t) (hhalf : 2 * t = Fintype.card V)
    (hthird : 2 * t ≤ 3 * X.card) (hXt : X.card ≤ t) :
    HasFractionalHalfBound G
      (min (((t : ℚ) / (Xᶜ.card : ℚ)) ^ 2 * (edgeCountOn G Xᶜ : ℚ))
        (completionEnvelope (X.card : ℚ) (t : ℚ) + (edgeCountOn G X : ℚ))) := by
  have hYcard : Xᶜ.card = 2 * t - X.card := by rw [Finset.card_compl, ← hhalf]
  have htY : t ≤ Xᶜ.card := by omega
  have hY : Xᶜ.Nonempty := Finset.card_pos.mp (by omega)
  exact fractional_bound_min G
    (uniform_side_fractional_half G Xᶜ hY t htY hhalf)
    (deletion_completion_even G htri X t hhalf hthird hXt)

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.uniform_side_fractional_half
#print axioms Erdos128.CompletionBridge.fractional_bound_min
#print axioms Erdos128.CompletionBridge.cut_two_witness_bound_even
