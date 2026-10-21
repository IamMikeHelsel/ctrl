import Mathlib.Tactic
namespace R07Critic

/-- Exact task trajectory for the declared M=diag(1,2), torque(1,-1), v0=0. -/
theorem torque_null_is_not_dynamic_null (t : ℝ) :
    (1:ℝ)+(-1)=0 ∧ ((1/5+t^2/2)+(-1/5-t^2/4))=t^2/4 := by
  constructor
  · norm_num
  · ring

theorem finite_step_leaves_regular_fiber (h : ℝ) (hh : h≠0) :
    (1:ℝ)^2+h^2>1 := by nlinarith [sq_pos_of_ne_zero hh]

theorem singular_fiber_is_singleton (x y : ℝ) (h : x^2+y^2=0) :
    x=0 ∧ y=0 := by
  constructor <;> nlinarith [sq_nonneg x,sq_nonneg y]

/-- Dynamic cancellation requires inertia-weighted allocation in this fixture. -/
theorem feasible_dynamic_null :
    (1/2:ℝ)+(-1)/2=0 ∧ |(1/2:ℝ)|≤1 ∧ |(-1:ℝ)|≤1 := by norm_num

/-- This is arithmetic of the declared maximal-braking trajectory, not a
formal differential-comparison proof for arbitrary measurable controls. -/
theorem stopping_witness :
    (9/10:ℝ)+1^2/(2*1)=7/5 ∧ (1:ℝ)<7/5 := by norm_num

#print axioms torque_null_is_not_dynamic_null
#print axioms finite_step_leaves_regular_fiber
#print axioms singular_fiber_is_singleton
#print axioms feasible_dynamic_null
#print axioms stopping_witness
end R07Critic
