import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignV10Critic
/-- The variable-threshold epigraph fails convexity even with positive depth. -/
theorem epigraph_midpoint_failure :
    (1 : ℝ) / 1 ≤ 1 ∧ (9 : ℝ) / 3 ≤ 3 ∧
    ¬ ((5 : ℝ) / 2 ≤ 2) := by norm_num
/-- Two translated fixed cameras, zero pixels: no finite zero-error point. -/
theorem no_zero_threshold (x z : ℝ) (hz : 0 < z)
    (h0 : x / z = 0) (h1 : (x - 1) / z = 0) : False := by
  have hn : z ≠ 0 := ne_of_gt hz
  have hx : x = 0 := (div_eq_zero_iff).mp h0 |>.resolve_right hn
  have hx1 : x - 1 = 0 := (div_eq_zero_iff).mp h1 |>.resolve_right hn
  linarith
/-- Every positive error threshold has an explicit finite positive-depth point. -/
theorem positive_threshold_witness (g : ℝ) (hg : 0 < g) :
    0 < 1 / (2 * g) ∧
    (1 / 2 : ℝ) / (1 / (2 * g)) = g ∧
    ((1 / 2 : ℝ) - 1) / (1 / (2 * g)) = -g := by
  have hn : g ≠ 0 := ne_of_gt hg
  constructor
  · positivity
  constructor <;> field_simp <;> ring
/-- Squared residual algebra alone loses both zero-depth and behind-camera exclusions. -/
theorem squared_depth_failure :
    (0 : ℝ)^2 ≤ 0^2 * (-1)^2 ∧ ¬ (0 < (-1 : ℝ)) ∧
    (0 : ℝ)^2 ≤ 0^2 * 0^2 ∧ ¬ (0 < (0 : ℝ)) := by norm_num
end CampaignV10Critic
#print axioms CampaignV10Critic.epigraph_midpoint_failure
#print axioms CampaignV10Critic.no_zero_threshold
#print axioms CampaignV10Critic.positive_threshold_witness
#print axioms CampaignV10Critic.squared_depth_failure
