import Mathlib.Tactic
namespace S07Critic
/-- Literal source held formulas, one common exponential parameter. -/
theorem current_request (x v a u t E : ℝ) :
 -(x+t*v+u*t^2/2+(a-u)*(t-1+E))-
 3*(v+u*t+(a-u)*(1-E))-2*(u+(a-u)*E) =
 (-x-3*v-2*a)-t*(v+a)-u*(2*t+t^2/2) := by ring
/-- Dropping the off-diagonal terms falsely admits this point. -/
theorem diagonal_false_admission :
 (451/40:ℝ)<12 ∧ 12<(5321/200:ℝ) ∧
 ((38/5:ℝ)+(1319/50)+(278/25))/4=451/40 ∧
 ((38/5:ℝ)+(1319/50)+(278/25)+2*(257/25)+10+2*(769/50))/4=5321/200 := by norm_num
/-- At source z=(0,0,1), clamp(-2)+.01 differs from clamp(-2+.01). -/
theorem disturbance_placement :
 max (-1:ℝ) (min 1 (-2)) + 1/100 = -99/100 ∧
 max (-1:ℝ) (min 1 (-2+1/100)) = -1 := by norm_num
/-- Long held interval negative; its five-unit horizon violates the source upper bound. -/
theorem long_hold_travel_failure (E : ℝ) (hE : E≤1) :
 -((5:ℝ)^2)/2+2*(5-1+E) < -2 := by nlinarith
end S07Critic
#print axioms S07Critic.current_request
#print axioms S07Critic.diagonal_false_admission
#print axioms S07Critic.disturbance_placement
#print axioms S07Critic.long_hold_travel_failure
