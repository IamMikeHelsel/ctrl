import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/- Declared two-dimensional goal-permission extension, not the scalar source task. -/
set_option autoImplicit false
namespace R01Critic

theorem disk_pairwise_witnesses :
    (1:ℝ)^2 + 0^2 ≤ 1 ∧ ((1:ℝ)-2)^2 + 0^2 ≤ 1 ∧
    (1/2:ℝ)^2 + (3/4)^2 ≤ 1 ∧ ((1/2:ℝ)-1)^2 + (3/4-3/2)^2 ≤ 1 ∧
    ((3/2:ℝ)-2)^2 + (3/4)^2 ≤ 1 ∧ ((3/2:ℝ)-1)^2 + (3/4-3/2)^2 ≤ 1 := by
  norm_num

theorem no_common_point (x y : ℝ)
    (ha : x^2 + y^2 ≤ 1)
    (hb : (x-2)^2 + y^2 ≤ 1)
    (hc : (x-1)^2 + (y-3/2)^2 ≤ 1) : False := by
  have hy : y = 0 := by nlinarith [sq_nonneg (x-1), sq_nonneg y]
  have hx : x = 1 := by nlinarith [sq_nonneg (x-1)]
  subst x
  subst y
  norm_num at hc

#print axioms disk_pairwise_witnesses
#print axioms no_common_point
end R01Critic
