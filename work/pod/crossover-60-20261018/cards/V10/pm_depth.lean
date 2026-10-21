import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignV10Depth

/-- Parallel calibrated cameras with unit baseline and both pixels at the origin. -/
theorem stereo_lower (x y z gamma : ℝ) (hz : 0 ≤ z) (hg : 0 ≤ gamma)
    (h1 : x^2 + y^2 ≤ (gamma*z)^2)
    (h2 : (x-1)^2 + y^2 ≤ (gamma*z)^2) : 1 ≤ 2*(gamma*z) := by
  have hp : 0 ≤ gamma*z := mul_nonneg hg hz
  have hs : (1/4 : ℝ) ≤ (gamma*z)^2 := by
    nlinarith [sq_nonneg (x-1/2), sq_nonneg y]
  nlinarith

/-- No finite point satisfies zero reprojection threshold. -/
theorem zero_threshold_infeasible (x y z : ℝ) (hz : 0 ≤ z)
    (h1 : x^2 + y^2 ≤ (0*z)^2)
    (h2 : (x-1)^2 + y^2 ≤ (0*z)^2) : False := by
  have h := stereo_lower x y z 0 hz (by norm_num) h1 h2
  norm_num at h

/-- Every positive threshold has a finite positive-depth witness. -/
theorem positive_threshold_witness (gamma : ℝ) (hg : 0 < gamma) :
    0 < 1/(2*gamma) ∧
    (1/2 : ℝ)^2 + 0^2 ≤ (gamma*(1/(2*gamma)))^2 ∧
    ((1/2 : ℝ)-1)^2 + 0^2 ≤ (gamma*(1/(2*gamma)))^2 := by
  have hn : gamma ≠ 0 := ne_of_gt hg
  have he : gamma*(1/(2*gamma)) = (1/2 : ℝ) := by field_simp
  rw [he]
  exact ⟨by positivity, by norm_num, by norm_num⟩

/-- An upper depth bound changes the model and restores this explicit optimum. -/
theorem capped_lower (x y z gamma cap : ℝ) (hz : 0 ≤ z) (hg : 0 ≤ gamma)
    (hcap : 0 < cap) (hzcap : z ≤ cap)
    (h1 : x^2 + y^2 ≤ (gamma*z)^2)
    (h2 : (x-1)^2 + y^2 ≤ (gamma*z)^2) : 1/(2*cap) ≤ gamma := by
  have h := stereo_lower x y z gamma hz hg h1 h2
  have hm := mul_le_mul_of_nonneg_left hzcap hg
  apply (div_le_iff₀ (by positivity : 0 < 2*cap)).2
  nlinarith

theorem capped_attainment (cap : ℝ) (hc : 0 < cap) :
    0 < cap ∧
    (1/2 : ℝ)^2 + 0^2 ≤ ((1/(2*cap))*cap)^2 ∧
    ((1/2 : ℝ)-1)^2 + 0^2 ≤ ((1/(2*cap))*cap)^2 := by
  have hn : cap ≠ 0 := ne_of_gt hc
  have he : (1/(2*cap))*cap = (1/2 : ℝ) := by field_simp
  rw [he]
  exact ⟨hc, by norm_num, by norm_num⟩

/-- A positive lower depth alone cannot prevent the escaping sequence. -/
theorem lower_depth_still_escapes (delta epsilon : ℝ) (hd : 0 < delta) (he : 0 < epsilon) :
    ∃ z : ℝ, delta ≤ z ∧ 0 < z ∧ 1/(2*z) ≤ epsilon := by
  refine ⟨max delta (1/(2*epsilon)), le_max_left _ _, ?_, ?_⟩
  · exact lt_of_lt_of_le hd (le_max_left _ _)
  · have hz : 0 < max delta (1/(2*epsilon)) := lt_of_lt_of_le hd (le_max_left _ _)
    apply (div_le_iff₀ (by positivity : 0 < 2*max delta (1/(2*epsilon)))).2
    have h := le_max_right delta (1/(2*epsilon))
    have hp : (1/(2*epsilon))*(2*epsilon) = (1:ℝ) := by field_simp
    have hm := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2*epsilon)
    nlinarith

end CampaignV10Depth
#print axioms CampaignV10Depth.stereo_lower
#print axioms CampaignV10Depth.zero_threshold_infeasible
#print axioms CampaignV10Depth.positive_threshold_witness
#print axioms CampaignV10Depth.capped_lower
#print axioms CampaignV10Depth.capped_attainment
#print axioms CampaignV10Depth.lower_depth_still_escapes
