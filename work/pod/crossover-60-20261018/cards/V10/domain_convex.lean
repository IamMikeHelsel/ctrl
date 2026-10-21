import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace CampaignV10
/-- Every norm cone with an affine right side is convex; camera residuals/depths
    must actually depend affinely on the optimization variables. -/
theorem cone_interpolation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (za zb gamma alpha beta : ℝ)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (h1 : ‖a‖ ≤ gamma*za) (h2 : ‖b‖ ≤ gamma*zb) :
    ‖alpha • a + beta • b‖ ≤ gamma*(alpha*za+beta*zb) := by
  calc
    ‖alpha • a + beta • b‖ ≤ ‖alpha • a‖ + ‖beta • b‖ := norm_add_le _ _
    _ = alpha*‖a‖ + beta*‖b‖ := by simp [norm_smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ alpha*(gamma*za)+beta*(gamma*zb) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = gamma*(alpha*za+beta*zb) := by ring

theorem positive_depth_interpolation (za zb alpha beta : ℝ)
    (hza : 0 < za) (hzb : 0 < zb) (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hsum : alpha+beta=1) : 0 < alpha*za+beta*zb := by
  by_cases h : 0 < alpha
  · have hp := mul_pos h hza
    have hn := mul_nonneg hb (le_of_lt hzb)
    linarith
  · have halpha : alpha=0 := le_antisymm (le_of_not_gt h) ha
    simp_all
end CampaignV10
#print axioms CampaignV10.cone_interpolation
#print axioms CampaignV10.positive_depth_interpolation
