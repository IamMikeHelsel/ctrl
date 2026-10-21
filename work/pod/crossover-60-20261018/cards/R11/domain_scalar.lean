import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
namespace CampaignR11
/-- Assumed scalar first-order relative-angle actuator; algebra, not an ODE existence proof. -/
theorem coordinated_error_equation (base q goal baseRate goalRate a delta w : ℝ)
    (ha : a ≠ 0) :
    baseRate + a*((goal-base+(goalRate-baseRate)/a+delta)-q)+w-goalRate =
      -a*(base+q-goal)+a*delta+w := by
  field_simp
  <;> ring

theorem missing_rate_bias (base q goal baseRate goalRate a w : ℝ) :
    baseRate+a*((goal-base)-q)+w-goalRate =
      -a*(base+q-goal)+(baseRate-goalRate)+w := by ring

/-- Conditional sample-age bound once the relative-position and rate differences
    are bounded at the SAME timestamp and in the SAME frame. -/
theorem command_age_bound (p v a age V A : ℝ) (ha : 0 < a)
    (hp : |p| ≤ V*age) (hv : |v| ≤ A*age) :
    |p+v/a| ≤ (V+A/a)*age := by
  calc
    |p+v/a| ≤ |p|+|v/a| := abs_add_le _ _
    _ = |p|+|v|/a := by rw [abs_div, abs_of_pos ha]
    _ ≤ V*age+(A*age)/a := add_le_add hp (div_le_div_of_nonneg_right hv (le_of_lt ha))
    _ = (V+A/a)*age := by ring

/-- The exact exponential solution's convex-envelope step preserves a tube. -/
theorem scalar_envelope (rho initial forcing tube : ℝ)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1) (hi : |initial| ≤ tube)
    (hf : |forcing| ≤ tube) : |rho*initial+(1-rho)*forcing| ≤ tube := by
  calc
    |rho*initial+(1-rho)*forcing| ≤ |rho*initial|+|(1-rho)*forcing| := abs_add_le _ _
    _ = rho*|initial|+(1-rho)*|forcing| := by
      simp only [abs_mul, abs_of_nonneg hr, abs_of_nonneg (sub_nonneg.mpr hr1)]
    _ ≤ rho*tube+(1-rho)*tube :=
      add_le_add (mul_le_mul_of_nonneg_left hi hr)
        (mul_le_mul_of_nonneg_left hf (by linarith))
    _ = tube := by ring

theorem declared_age_budget :
    ((1/10:ℝ)+1+(1+10)/40)*(3/1000)+(1/100)/40 = 7/1600 ∧
    (7/1600:ℝ) < 1/200 := by norm_num

/-- Prospective no-clipping closure includes both the error tube and held command error. -/
theorem declared_actuator_budget :
    (1/10:ℝ)+1+40*(1/200)+40*(33/8000) = 293/200 ∧
    (293/200:ℝ) < 3/2 := by norm_num
/-- Disturbance w also contributes to actual physical relative angular velocity. -/
theorem actual_rate_budget :
    (293/200:ℝ)+1/100 = 59/40 ∧ (59/40:ℝ) < 3/2 := by norm_num
end CampaignR11
#print axioms CampaignR11.coordinated_error_equation
#print axioms CampaignR11.missing_rate_bias
#print axioms CampaignR11.command_age_bound
#print axioms CampaignR11.scalar_envelope
#print axioms CampaignR11.declared_age_budget
#print axioms CampaignR11.declared_actuator_budget

#print axioms CampaignR11.actual_rate_budget
