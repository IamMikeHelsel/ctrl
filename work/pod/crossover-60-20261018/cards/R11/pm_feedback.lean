import Mathlib.Tactic
namespace CampaignR11Feedback
/-- Constant residual shifts the equilibrium. -/
theorem constant_shift (x y z eta : ℝ) :
  x-(y+eta)/10-(z+eta)/10+eta =
  (x+eta)-(y+eta)/10-(z+eta)/10 := by ring
/-- Measured output recurrence is driven by residual increments. -/
theorem increment_input (x y z e0 e1 e2 en : ℝ) :
  x-(y+e1)/10-(z+e2)/10+en =
  (x+e0)-(y+e1)/10-(z+e2)/10+(en-e0) := by ring
/-- Inner bias cancels at equilibrium while measurement bias remains. -/
theorem equilibrium_physical (g e n : ℝ) : (g-(e+n))+e-g = -n := by ring
/-- Amplitude-only admission permits an acceleration violation. -/
theorem alternating_failure :
  (10*(23/5000-(-23/5000))/(1/50):ℝ) = 23/5 ∧
  (23/5:ℝ) > 1 ∧ (10*(23/5000):ℝ) < 1/10 := by norm_num
end CampaignR11Feedback
#print axioms CampaignR11Feedback.constant_shift
#print axioms CampaignR11Feedback.increment_input
#print axioms CampaignR11Feedback.equilibrium_physical
#print axioms CampaignR11Feedback.alternating_failure
