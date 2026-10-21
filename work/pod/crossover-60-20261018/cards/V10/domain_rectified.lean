import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace CampaignV10
/-- For rectified stereo s=B/z>0, d=u1-u2,c=v2-v1, the two pixel
    residuals can be written (a,b),(a-(s-d),b-c). -/
theorem rectified_residual_identity (a b s d c : ℝ) :
    (a^2+b^2)+((a-(s-d))^2+(b-c)^2) =
    2*((a-(s-d)/2)^2+(b-c/2)^2)+((s-d)^2+c^2)/2 := by ring

theorem rectified_threshold_lower (a b s d c gamma : ℝ)
    (h1 : a^2+b^2 ≤ gamma^2)
    (h2 : (a-(s-d))^2+(b-c)^2 ≤ gamma^2) :
    (s-d)^2+c^2 ≤ 4*gamma^2 := by
  have hi := rectified_residual_identity a b s d c
  nlinarith [sq_nonneg (a-(s-d)/2),sq_nonneg (b-c/2)]

theorem rectified_balanced_residual (s d c : ℝ) :
    ((s-d)/2)^2+(c/2)^2 = ((s-d)^2+c^2)/4 ∧
    (((s-d)/2)-(s-d))^2+((c/2)-c)^2 = ((s-d)^2+c^2)/4 := by
  constructor <;> ring

/-- Nonpositive observed disparity cannot attain the limiting threshold at finite depth. -/
theorem nonpositive_disparity_strict_gap (s d c : ℝ) (hs : 0 < s) (hd : d ≤ 0) :
    d^2+c^2 < (s-d)^2+c^2 := by
  have hsd : s*d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs) hd
  nlinarith [sq_pos_of_pos hs]
/-- At positive disparity the unique minimizer s=d is in the finite-depth domain. -/
theorem positive_disparity_minimizer (d c : ℝ) (hd : 0 < d) :
    0 < d ∧ ((d-d)^2+c^2)/4 = c^2/4 ∧
    ∀ s : ℝ, c^2/4 ≤ ((s-d)^2+c^2)/4 := by
  refine ⟨hd, by ring, fun s => ?_⟩
  nlinarith [sq_nonneg (s-d)]

theorem positive_disparity_unique_equality (s d c : ℝ) :
    ((s-d)^2+c^2)/4 = c^2/4 ↔ s=d := by
  constructor
  · intro h
    nlinarith [sq_nonneg (s-d)]
  · intro h
    rw [h]
    ring

/-- Explicit vanishing gap as s tends to zero; convergence itself is not asserted. -/
theorem zero_depth_inverse_gap_identity (s d c : ℝ) :
    ((s-d)^2+c^2)/4-(d^2+c^2)/4 = (s^2-2*s*d)/4 := by ring

end CampaignV10
#print axioms CampaignV10.rectified_residual_identity
#print axioms CampaignV10.rectified_threshold_lower
#print axioms CampaignV10.rectified_balanced_residual
#print axioms CampaignV10.nonpositive_disparity_strict_gap

#print axioms CampaignV10.positive_disparity_minimizer
#print axioms CampaignV10.positive_disparity_unique_equality
#print axioms CampaignV10.zero_depth_inverse_gap_identity
