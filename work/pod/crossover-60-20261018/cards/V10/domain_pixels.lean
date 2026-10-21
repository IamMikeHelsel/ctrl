import domain_cones
namespace CampaignV10
/-- These are the literal projections of P1=[I|0],P2=[I|(-1,0,0)],
    compared to observed pixels (0,0),(-1,1/2), in Euclidean image distance. -/
theorem pixel_bounds_to_cones (x y z gamma : ℝ) (hz : 0 < z) (hg : 0 ≤ gamma)
    (h1 : Real.sqrt ((x/z)^2+(y/z)^2) ≤ gamma)
    (h2 : Real.sqrt (((x-1)/z+1)^2+(y/z-1/2)^2) ≤ gamma) :
    x^2+y^2 ≤ (gamma*z)^2 ∧
    (x+z-1)^2+(y-z/2)^2 ≤ (gamma*z)^2 := by
  have h1s := (Real.sqrt_le_left hg).mp h1
  have h2s := (Real.sqrt_le_left hg).mp h2
  have h1c := (squared_threshold_iff x y z 0 0 gamma hz).mp (by simpa using h1s)
  have h2c := (squared_threshold_iff (x-1) y z (-1) (1/2) gamma hz).mp (by simpa using h2s)
  constructor
  · simpa using h1c
  · convert h2c using 1 <;> ring

theorem actual_pixel_global_lower (x y z gamma : ℝ) (hz : 0 < z) (hg : 0 ≤ gamma)
    (h1 : Real.sqrt ((x/z)^2+(y/z)^2) ≤ gamma)
    (h2 : Real.sqrt (((x-1)/z+1)^2+(y/z-1/2)^2) ≤ gamma) : 1/4 ≤ gamma := by
  obtain ⟨ha,hb⟩ := pixel_bounds_to_cones x y z gamma hz hg h1 h2
  exact fixed_camera_global_lower x y z gamma hz hg ha hb

theorem actual_pixel_optimum_unique (x y z : ℝ) (hz : 0 < z)
    (h1 : Real.sqrt ((x/z)^2+(y/z)^2) ≤ 1/4)
    (h2 : Real.sqrt (((x-1)/z+1)^2+(y/z-1/2)^2) ≤ 1/4) :
    x=0 ∧ y=1/4 ∧ z=1 := by
  obtain ⟨ha,hb⟩ := pixel_bounds_to_cones x y z (1/4) hz (by norm_num) h1 h2
  exact optimum_unique x y z hz ha hb

theorem actual_pixel_attainment :
    Real.sqrt (((0:ℝ)/1)^2+((1/4)/1)^2) ≤ 1/4 ∧
    Real.sqrt ((((0:ℝ)-1)/1+1)^2+((1/4)/1-1/2)^2) ≤ 1/4 := by
  constructor <;> rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 1/4)] <;> norm_num
end CampaignV10
#print axioms CampaignV10.pixel_bounds_to_cones
#print axioms CampaignV10.actual_pixel_global_lower
#print axioms CampaignV10.actual_pixel_optimum_unique
#print axioms CampaignV10.actual_pixel_attainment
