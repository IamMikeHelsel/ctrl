import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CampaignV10
/-- The two-dimensional squared Euclidean reprojection residual scales by z². -/
theorem reprojection_scaling (a b z u v : ℝ) (hz : z ≠ 0) :
    (a / z - u)^2 + (b / z - v)^2 =
      ((a - u*z)^2 + (b - v*z)^2) / z^2 := by
  field_simp

/-- Positive depth binds the image-plane threshold to its cone inequality.
    Nonnegative gamma is a semantic premise when these squares represent a norm bound. -/
theorem squared_threshold_iff (a b z u v gamma : ℝ) (hz : 0 < z) :
    ((a / z - u)^2 + (b / z - v)^2 ≤ gamma^2) ↔
    ((a-u*z)^2 + (b-v*z)^2 ≤ (gamma*z)^2) := by
  rw [reprojection_scaling a b z u v (ne_of_gt hz)]
  rw [div_le_iff₀ (sq_pos_of_pos hz)]
  ring_nf

/-- An elementary dual bound: two vertical residual slabs force gamma≥1/4. -/
theorem vertical_lower_bound (y z gamma : ℝ) (hz : 0 < z)
    (h1 : y ≤ gamma*z) (h2 : -(y-z/2) ≤ gamma*z) :
    1/4 ≤ gamma := by
  nlinarith

/-- Euclidean squared cones imply their signed vertical slab inequalities. -/
theorem cone_vertical_bounds (x y z gamma : ℝ) (hz : 0 ≤ z) (hg : 0 ≤ gamma)
    (h1 : x^2+y^2 ≤ (gamma*z)^2)
    (h2 : (x+z-1)^2+(y-z/2)^2 ≤ (gamma*z)^2) :
    y ≤ gamma*z ∧ -(y-z/2) ≤ gamma*z := by
  have hgz : 0 ≤ gamma*z := mul_nonneg hg hz
  constructor
  · nlinarith [sq_nonneg x, sq_nonneg (y+gamma*z)]
  · nlinarith [sq_nonneg (x+z-1), sq_nonneg (y-z/2-gamma*z)]

theorem fixed_camera_global_lower (x y z gamma : ℝ) (hz : 0 < z) (hg : 0 ≤ gamma)
    (h1 : x^2+y^2 ≤ (gamma*z)^2)
    (h2 : (x+z-1)^2+(y-z/2)^2 ≤ (gamma*z)^2) : 1/4 ≤ gamma := by
  obtain ⟨ha,hb⟩ := cone_vertical_bounds x y z gamma (le_of_lt hz) hg h1 h2
  exact vertical_lower_bound y z gamma hz ha hb

theorem fixed_camera_attained :
    (0 : ℝ) < 1 ∧
    (0 : ℝ)^2+(1/4)^2 ≤ ((1/4)*1)^2 ∧
    ((0 : ℝ)+1-1)^2+((1/4)-1/2)^2 ≤ ((1/4)*1)^2 := by norm_num

theorem fifth_threshold_infeasible (x y z : ℝ) (hz : 0 < z)
    (h1 : x^2+y^2 ≤ ((1/5)*z)^2)
    (h2 : (x+z-1)^2+(y-z/2)^2 ≤ ((1/5)*z)^2) : False := by
  have h := fixed_camera_global_lower x y z (1/5) hz (by norm_num) h1 h2
  norm_num at h

theorem optimum_unique (x y z : ℝ) (hz : 0 < z)
    (h1 : x^2+y^2 ≤ ((1/4)*z)^2)
    (h2 : (x+z-1)^2+(y-z/2)^2 ≤ ((1/4)*z)^2) :
    x = 0 ∧ y = 1/4 ∧ z = 1 := by
  obtain ⟨ha,hb⟩ := cone_vertical_bounds x y z (1/4) (le_of_lt hz) (by norm_num) h1 h2
  have hy : y = z/4 := by linarith
  have hx : x = 0 := by rw [hy] at h1; nlinarith [sq_nonneg x]
  have hz1 : z = 1 := by rw [hx,hy] at h2; nlinarith [sq_nonneg (z-1)]
  exact ⟨hx, by rw [hy,hz1], hz1⟩
/-- Euclidean error is the square root of the sum of squared image residuals. -/
theorem euclidean_threshold_iff (a b z u v gamma : ℝ) (hz : 0 < z)
    (hg : 0 ≤ gamma) :
    Real.sqrt ((a / z - u)^2 + (b / z - v)^2) ≤ gamma ↔
      Real.sqrt ((a-u*z)^2+(b-v*z)^2) ≤ gamma*z := by
  rw [Real.sqrt_le_left hg, Real.sqrt_le_left (mul_nonneg hg (le_of_lt hz))]
  exact squared_threshold_iff a b z u v gamma hz
end CampaignV10
#print axioms CampaignV10.reprojection_scaling
#print axioms CampaignV10.squared_threshold_iff
#print axioms CampaignV10.vertical_lower_bound
#print axioms CampaignV10.cone_vertical_bounds
#print axioms CampaignV10.fixed_camera_global_lower
#print axioms CampaignV10.fixed_camera_attained
#print axioms CampaignV10.fifth_threshold_infeasible
#print axioms CampaignV10.optimum_unique

#print axioms CampaignV10.euclidean_threshold_iff
