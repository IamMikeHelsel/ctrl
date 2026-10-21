import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignR11Outer

/-- Matched first-order servo plus continuous reference: derivatives are premises. -/
theorem inner_error_identity (a beta q r betadot v disturbance : ℝ) (ha : a ≠ 0) :
    betadot + (a * ((r-beta+(v-betadot)/a)-q) + disturbance) - v =
    -a*(beta+q-r)+disturbance := by field_simp; ring

/-- Exact two-sample recurrence energy, no delay-free surrogate. -/
theorem delayed_energy (x y gain : ℝ) :
    (x-gain*y)^2 - (x-gain*y)*x + gain*x^2 =
    gain*(x^2-x*y+gain*y^2) := by ring

theorem positive_energy_decomposition (x y gain : ℝ) :
    x^2-x*y+gain*y^2 = (x-y/2)^2+(gain-1/4)*y^2 := by ring

theorem unstable_gain_positive (x y : ℝ) :
    (1/2 : ℝ)*(x^2+y^2) ≤ x^2-x*y+(6/5)*y^2 := by
  nlinarith [sq_nonneg (x-y),sq_nonneg y]

theorem stable_gain_positive (x y : ℝ) :
    (1/8 : ℝ)*(x^2+y^2) ≤ x^2-x*y+(1/2)*y^2 := by
  nlinarith [sq_nonneg (x-y),sq_nonneg (x-2*y)]

theorem stable_gain_upper (x y : ℝ) :
    x^2-x*y+(1/2)*y^2 ≤ (3/2 : ℝ)*(x^2+y^2) := by
  nlinarith [sq_nonneg (x+y),sq_nonneg y]

theorem delay_free_contraction (x : ℝ) :
    ((1-(6/5 : ℝ))*x)^2 = (1/25 : ℝ)*x^2 := by ring

/-- Slow visual law with one-sample age and consistent continuous reference. -/
theorem outer_sample_identity (r previous goal h k : ℝ) :
    (r+h*(-k*(previous-goal)))-goal = (r-goal)-(h*k)*(previous-goal) := by ring

/-- Base rate authority cannot be repaired by bookkeeping. -/
theorem rate_authority_obstruction (betaRate qRate authority : ℝ)
    (h : -authority ≤ qRate) : betaRate-authority ≤ betaRate+qRate := by linarith

end CampaignR11Outer
#print axioms CampaignR11Outer.inner_error_identity
#print axioms CampaignR11Outer.delayed_energy
#print axioms CampaignR11Outer.positive_energy_decomposition
#print axioms CampaignR11Outer.unstable_gain_positive
#print axioms CampaignR11Outer.stable_gain_positive
#print axioms CampaignR11Outer.stable_gain_upper
#print axioms CampaignR11Outer.delay_free_contraction
#print axioms CampaignR11Outer.outer_sample_identity
#print axioms CampaignR11Outer.rate_authority_obstruction
