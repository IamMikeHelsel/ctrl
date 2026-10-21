import domain_rectified
namespace CampaignV10
/-- Literal affine camera projection to the residual-difference coordinates. -/
theorem rectified_pixel_difference (x y z baseline u1 u2 v1 v2 : ℝ) :
    ((x-baseline)/z-u2) = (x/z-u1)-(baseline/z-(u1-u2)) ∧
    (y/z-v2) = (y/z-v1)-(v2-v1) := by
  constructor
  · simp only [sub_div]
    ring
  · ring

/-- Every finite positive-depth pixel pair obeys the reduced objective bound. -/
theorem rectified_pixel_lower (x y z baseline u1 u2 v1 v2 gamma : ℝ)
    (h1 : (x/z-u1)^2+(y/z-v1)^2 ≤ gamma^2)
    (h2 : ((x-baseline)/z-u2)^2+(y/z-v2)^2 ≤ gamma^2) :
    (baseline/z-(u1-u2))^2+(v2-v1)^2 ≤ 4*gamma^2 := by
  obtain ⟨hx,hy⟩ := rectified_pixel_difference x y z baseline u1 u2 v1 v2
  rw [hx,hy] at h2
  exact rectified_threshold_lower (x/z-u1) (y/z-v1) (baseline/z) (u1-u2) (v2-v1) gamma h1 h2

/-- At each chosen inverse depth s>0, the balanced pair is realized by a real
    finite point; this supplies the converse half of the scalar reduction. -/
theorem rectified_balanced_point (baseline s u1 u2 v1 v2 : ℝ)
    (hB : 0 < baseline) (hs : 0 < s) :
    ∃ x y z : ℝ, 0 < z ∧ baseline/z=s ∧
      (x/z-u1)^2+(y/z-v1)^2 = ((s-(u1-u2))^2+(v2-v1)^2)/4 ∧
      ((x-baseline)/z-u2)^2+(y/z-v2)^2 = ((s-(u1-u2))^2+(v2-v1)^2)/4 := by
  have hBn : baseline ≠ 0 := ne_of_gt hB
  have hsn : s ≠ 0 := ne_of_gt hs
  refine ⟨(baseline/s)*(u1+(s-(u1-u2))/2),
    (baseline/s)*(v1+(v2-v1)/2), baseline/s, div_pos hB hs, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
    <;> ring
  · field_simp
    <;> ring
end CampaignV10
#print axioms CampaignV10.rectified_pixel_difference
#print axioms CampaignV10.rectified_pixel_lower
#print axioms CampaignV10.rectified_balanced_point
