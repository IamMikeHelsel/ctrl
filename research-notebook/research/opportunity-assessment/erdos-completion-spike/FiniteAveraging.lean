import ProfileBound
import AveragingBridge
set_option maxHeartbeats 1000000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The finite variance inequality with an explicitly specified mean. -/
theorem sum_sq_ge_card_mul_mean_sq (S : Finset V) (r : V → ℚ) (R : ℚ)
    (hmean : ∑ v ∈ S, r v = (S.card : ℚ) * R) :
    (S.card : ℚ) * R ^ 2 ≤ ∑ v ∈ S, (r v) ^ 2 := by
  have hvar := Finset.sum_nonneg (s := S) (fun v _ => sq_nonneg (r v - R))
  have heq : (∑ v ∈ S, (r v - R) ^ 2) =
      (∑ v ∈ S, (r v) ^ 2) - 2 * R * (∑ v ∈ S, r v) + (S.card : ℚ) * R ^ 2 := by
    simp_rw [show ∀ v, (r v - R) ^ 2 = (r v) ^ 2 - 2 * R * r v + R ^ 2 by intro v; ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  rw [heq, hmean] at hvar
  nlinarith

/-- Finite averaging and witness selection for a concave quadratic tail.
The next graph theorem instantiates cost with actual feasible-profile cost. -/
theorem exists_le_concave_average
    (S : Finset V) (hne : S.Nonempty) (cost cross r : V → ℚ)
    (A L C M R : ℚ) (hC : 0 ≤ C)
    (hcost : ∀ v ∈ S, cost v ≤ A + cross v + L * r v - C * (r v) ^ 2)
    (hcross : (∑ v ∈ S, cross v) ≤ (S.card : ℚ) * M)
    (hmean : (∑ v ∈ S, r v) = (S.card : ℚ) * R) :
    ∃ v ∈ S, cost v ≤ A + M + L * R - C * R ^ 2 := by
  have hs := Finset.sum_le_sum hcost
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hs
  have hv := sum_sq_ge_card_mul_mean_sq S r R hmean
  have hvC := mul_le_mul_of_nonneg_left hv hC
  have hsum : (∑ v ∈ S, cost v) ≤
      ∑ _v ∈ S, (A + M + L * R - C * R ^ 2) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hmean] at hs
    nlinarith
  exact Finset.exists_le_of_sum_le hne hsum

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.sum_sq_ge_card_mul_mean_sq
#print axioms Erdos128.CompletionBridge.exists_le_concave_average
