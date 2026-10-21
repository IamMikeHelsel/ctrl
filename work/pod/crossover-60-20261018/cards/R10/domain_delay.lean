import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace R10RetainedDelay
/-- Fixed h=.2, equal opposite deltas .02; alpha is execution separation/h.
The old response lies on normalized segment[2,3], the new one on[1,2]. -/
theorem reversal_acceleration_formula (s alpha : ℝ) :
    (1/2)*((3/2)*s^2-8*s+10 - (-(3/2)*(s-alpha)^2+4*(s-alpha)-2)) =
      (3/2)*(s-(2+alpha/2))^2+3*alpha^2/8-alpha := by ring

theorem critical_point_branches (alpha : ℝ) (hlo : 3/2≤alpha) (hhi : alpha≤2) :
    2 ≤ 2+alpha/2 ∧ 2+alpha/2 ≤ 3 ∧
    1 ≤ (2+alpha/2)-alpha ∧ (2+alpha/2)-alpha ≤ 2 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- For ready-time separation .3 through .4, meeting A=.5 requires the full .4.
This is a necessary condition within this delayed-one-event family, not all planners. -/
theorem minimal_delay_in_family (alpha : ℝ) (hlo : 3/2≤alpha) (hhi : alpha≤2)
    (ha : |3*alpha^2/8-alpha|≤1/2) : alpha=2 := by
  have h := (abs_le.mp ha).1
  have hp : 0≤(2-alpha)*(alpha-3/2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- New proposal execution .62 preserves old .22 event and reaches its reference tail1.42.
The source buffered case has both executions shifted later by .06. -/
theorem delayed_reference_arithmetic :
    (11/50:ℝ)+2*(1/5)=31/50 ∧
    (31/50:ℝ)-13/25=1/10 ∧
    (31/50:ℝ)+4*(1/5)=71/50 ∧
    (71/50:ℝ)<17/10 ∧
    (7/25:ℝ)-3/50=11/50 ∧ (17/25:ℝ)-3/50=31/50 ∧
    |3*(2:ℝ)^2/8-2|=1/2 := by norm_num
#print axioms reversal_acceleration_formula
#print axioms critical_point_branches
#print axioms minimal_delay_in_family
#print axioms delayed_reference_arithmetic
end R10RetainedDelay
