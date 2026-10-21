import Mathlib.Tactic
namespace V01Gauge

theorem normalized_gauge (a x z : ℝ) (ha : a≠0) :
    (a*x)/(a*z)=x/z := by
  simp [mul_div_mul_left,ha]

theorem unoriented_threshold {r q tau : ℝ} (hq : q≠0) :
    |r/q|≤tau/|q| ↔ |r|≤tau := by
  rw [abs_div]
  exact div_le_div_iff_of_pos_right (abs_pos.mpr hq)

theorem physical_depth_ratio {a z d1 d2 : ℝ} (ha : a≠0) (hd1 : d1≠0)
    (h : z=a*(d2/d1)) : z/a=d2/d1 := by
  rw [h]
  field_simp

theorem positive_depth_in_signed_gauge {a z d1 d2 : ℝ}
    (ha : a≠0) (hd1 : 0<d1) (h : z=a*(d2/d1)) :
    0<z/a ↔ 0<d2 := by
  rw [physical_depth_ratio ha (ne_of_gt hd1) h]
  exact div_pos_iff_of_pos_right hd1

#print axioms normalized_gauge
#print axioms unoriented_threshold
#print axioms physical_depth_ratio
#print axioms positive_depth_in_signed_gauge
end V01Gauge
