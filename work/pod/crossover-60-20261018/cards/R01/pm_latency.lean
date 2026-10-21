import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- AI-written isolated information-arrival necessary condition. Millimetres/seconds
   in numerical example. Speed-bound premise is a separate toy plant assumption,
   not imported from the original four-box closed-loop theorem. -/
set_option autoImplicit false
namespace R01Latency

theorem information_arrival_necessary
    (epsilon delta speed deadline arrival before after : ℝ)
    (common_hold : before ≤ epsilon)
    (move_success : delta - epsilon ≤ after)
    (finite_travel : after - before ≤ speed * (deadline-arrival)) :
    delta - 2*epsilon ≤ speed * (deadline-arrival) := by
  linarith

theorem late_truth_cannot_repair
    (before after : ℝ) (common_hold : before ≤ 1/5)
    (move_success : 1 - 1/5 ≤ after)
    (finite_travel : after - before ≤ 1*(1-(1/2:ℝ))) : False := by
  linarith

theorem tight_scalar_bound :
    (1:ℝ)-2*(1/5) = 1*(1-(2/5)) := by norm_num

#print axioms information_arrival_necessary
#print axioms late_truth_cannot_repair
#print axioms tight_scalar_bound
end R01Latency
