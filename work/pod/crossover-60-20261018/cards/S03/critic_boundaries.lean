import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
namespace S03Critic
/-- The center is in the source invariant, while a point strictly inside its decimal ADC cell is not. -/
theorem center_is_not_cell :
  (5*(-1/20:ℝ)^2+2*(-1/20)*(7/20)+(7/20)^2=1/10) ∧
  (5*(-1249/25000:ℝ)^2+2*(-1249/25000)*(8751/25000)+(8751/25000)^2>1/10) ∧
  (-1/20000:ℝ)<(-1249/25000)-(-1/20) ∧
  (-1249/25000:ℝ)-(-1/20)<1/20000 ∧
  (-1/20000:ℝ)<(8751/25000)-(7/20) ∧
  (8751/25000:ℝ)-(7/20)<1/20000 := by norm_num
/-- Zero control after rejecting that cell violates endpoint energy; not a source fallback. -/
theorem zero_fallback_unsafe :
  (5*((-1/20:ℝ)+(1/2)*(7/20))^2+
  2*((-1/20:ℝ)+(1/2)*(7/20))*(7/20)+(7/20)^2)=461/1600 ∧
  (461/1600:ℝ)>1/10 := by norm_num
/-- Exact current-state control error from the declared stale reading. -/
theorem stale_error :
  |(-3/10:ℝ)-(-2*(1/5000)-3*(1/10))|=1/2500 ∧
  (1/2500:ℝ)>1/4000 := by norm_num
end S03Critic
#print axioms S03Critic.center_is_not_cell
#print axioms S03Critic.zero_fallback_unsafe
#print axioms S03Critic.stale_error
