import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignR11Critic
/-- Same actuator position, two indistinguishable base angles separated by2a. -/
theorem indistinguishable_error_lower (q a : ℝ) :
    a ≤ max |q+a| |q-a| := by
  have h1 := le_abs_self (q+a)
  have h2 := neg_le_abs (q-a)
  have hm1 := le_max_left |q+a| |q-a|
  have hm2 := le_max_right |q+a| |q-a|
  linarith
/-- Endpoint consequence only; a causal-policy/data identity bridge is external. -/
theorem blackout_floor (q acceleration age : ℝ) :
    acceleration*age^2/2 ≤
      max |q+acceleration*age^2/2| |q-acceleration*age^2/2| := by
  convert indistinguishable_error_lower q (acceleration*age^2/2) using 1 <;> ring

theorem centered_prediction_sharp (a : ℝ) (ha : 0 ≤ a) :
    max |(0:ℝ)+a| |(0:ℝ)-a| = a := by simp [abs_of_nonneg ha]

theorem declared_blackout_budget :
    (2:ℝ)*(1/50)^2/2 = 1/2500 ∧ (1/10000:ℝ) < 1/2500 := by norm_num
/-- Ordinary kinematic frame sum does not cancel actual actuator tracking error. -/
theorem frame_error_identity (base joint goal desiredJoint : ℝ)
    (h : desiredJoint=goal-base) : base+joint-goal=joint-desiredJoint := by linarith
/-- First-order angle actuator, nominal inverse cancellation; derivatives are supplied. -/
theorem nominal_inverse_residual (base joint goal baseRate goalRate r nominal qdot : ℝ)
    (hn : nominal ≠ 0)
    (hplant : qdot=r*(goal-base+(goalRate-baseRate)/nominal-joint)) :
    baseRate+qdot-goalRate =
      -r*(base+joint-goal)+(1-r/nominal)*(baseRate-goalRate) := by
  rw [hplant]
  field_simp
  ring
end CampaignR11Critic
#print axioms CampaignR11Critic.indistinguishable_error_lower
#print axioms CampaignR11Critic.blackout_floor
#print axioms CampaignR11Critic.centered_prediction_sharp
#print axioms CampaignR11Critic.declared_blackout_budget
#print axioms CampaignR11Critic.frame_error_identity
#print axioms CampaignR11Critic.nominal_inverse_residual
