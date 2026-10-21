import Mathlib.Tactic
namespace C11Critic
/-- Same C3 center and full-state sensor corner; the third facet is attained. -/
theorem initial_corner :
  (-(1:ℝ)/1000 - (-(1:ℝ)/5/4+(72:ℝ)/625/32) +
    (-(1:ℝ)/5-1/100)/2+((72:ℝ)/625-1/20)/16) = -(2221:ℝ)/40000 := by norm_num

/-- Exact constant-rate8 pending flow; E is exp(-8t) in the ODE interpretation. -/
theorem pending_flow_coordinate (t E : ℝ) :
  ((-1/1000 : ℝ)+(-21/100)*t+(-121/100)*t^2/2+
    (797/625)*(t/8-(1-E)/64)) - (-29/625) +
  ((-21/100 : ℝ)+(-121/100)*t+(797/625)*(1-E)/8)/2 +
  ((-121/100 : ℝ)+(797/625)*E)/16 =
  -2221/40000 - (1639/2500)*t - (121/200)*t^2 + (797/40000)*(E-1) := by ring

/-- A concrete legal positive startup cannot stay in the same initial cube. -/
theorem pending_strict_escape (t E : ℝ) (ht : 0<t) (hE : E≤1) :
  -2221/40000 - (1639/2500)*t - (121/200)*t^2 + (797/40000)*(E-1)
    < -(2221:ℝ)/40000 := by nlinarith [sq_nonneg t]

/-- Universal conjunction requires every facet maximum, not a shared maximizer. -/
theorem conjunction_forall {X : Type*} (P Q : X → Prop) :
    (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by aesop
end C11Critic
#print axioms C11Critic.initial_corner
#print axioms C11Critic.pending_flow_coordinate
#print axioms C11Critic.pending_strict_escape
#print axioms C11Critic.conjunction_forall
