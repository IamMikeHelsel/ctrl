import Mathlib.Tactic
import Mathlib.Data.BitVec
namespace S03Inventor

theorem invariant_projection (x v : ℝ)
    (h : 5*x^2+2*x*v+v^2 ≤ 1/10) :
    |x| ≤ 159/1000 ∧ |v| ≤ 177/500 := by
  have hx : 4*x^2 ≤ 1/10 := by nlinarith [sq_nonneg (x+v)]
  have hv : 4*v^2 ≤ 1/2 := by nlinarith [sq_nonneg (5*x+v)]
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (x-159/1000), sq_nonneg (x+159/1000)]
  · apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (v-177/500), sq_nonneg (v+177/500)]

theorem q14_dot_bound (X V : ℤ)
    (hx : -2606 ≤ X ∧ X ≤ 2606) (hv : -5801 ≤ V ∧ V ≤ 5801) :
    -22615 ≤ -2*X-3*V ∧ -2*X-3*V ≤ 22615 := by omega

theorem q14_intermediates (X V : ℤ)
    (hx : -2606 ≤ X ∧ X ≤ 2606) (hv : -5801 ≤ V ∧ V ≤ 5801) :
    (-32768 ≤ -2*X ∧ -2*X ≤ 32767) ∧
    (-32768 ≤ -3*V ∧ -3*V ≤ 32767) ∧
    (-32768 ≤ -2*X-3*V ∧ -2*X-3*V ≤ 32767) := by omega

theorem q16_wrap_product : ((22938 : BitVec 16)*3).toInt = 3278 := by decide

theorem q16_wrap_output :
    ((-2 : BitVec 16)*(-3277 : BitVec 16)-3*(22938 : BitVec 16)).toInt = 3276 := by decide

theorem q16_wide_output :
    ((-2 : BitVec 32)*(-3277 : BitVec 32)-3*(22938 : BitVec 32)).toInt = -62260 := by decide

theorem valid_boundary :
    5*(-1/20:ℝ)^2+2*(-1/20)*(7/20)+(7/20)^2 = 1/10 := by norm_num

theorem format_budgets : (5/32768:ℝ) ≤ 1/4000 ∧ (5/131072:ℝ) ≤ 1/4000 := by norm_num

theorem zero_sum_errors_not_zero_state (e : ℝ) :
    let h : ℝ := 1/2
    let x1 := h^2*e/2
    let v1 := h*e
    let u1 := -2*x1-3*v1-e
    x1+h*v1+h^2*u1/2 = e/32 ∧ v1+h*u1 = -7*e/8 := by
  dsimp
  constructor <;> ring

end S03Inventor
#print axioms S03Inventor.invariant_projection
#print axioms S03Inventor.q14_dot_bound
#print axioms S03Inventor.q14_intermediates
#print axioms S03Inventor.q16_wrap_product
#print axioms S03Inventor.q16_wrap_output
#print axioms S03Inventor.q16_wide_output
#print axioms S03Inventor.valid_boundary
#print axioms S03Inventor.format_budgets
#print axioms S03Inventor.zero_sum_errors_not_zero_state
