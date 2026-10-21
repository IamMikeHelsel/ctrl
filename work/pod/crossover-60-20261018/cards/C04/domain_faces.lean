import Mathlib.Tactic
/-! Same physical coordinates and gains as the source; isolated face arithmetic.
No trajectory theorem or increased-age Execution is assumed to follow. -/
namespace C04Faces

theorem general_gain_coordinate_identity (p q h r x v a w : ℝ) :
    v+a/2+r*(-p*x-q*v-h*a+w-a)/16 =
      (4+r*(-p/16+q/4-h-1))*x +
      (-12+r*(-q/4+2*h+2))*(x+v/4) +
      (8-r*(h+1))*(x+v/2+a/16)+r*w/16 := by ring

theorem general_gain_slope_identity (p q h r x v a w : ℝ) :
    -p*v-q*a-h*r*(-p*x-q*v-h*a+w-a) =
      (4*p-16*q-h*r*(-p+4*q-16*h-16))*x +
      (-4*p+32*q-h*r*(-4*q+32*h+32))*(x+v/4) +
      (-16*q-h*r*(-16*h-16))*(x+v/2+a/16)-h*r*w := by ring

/-- Exact baseline weighted-box last-face condition. Other faces depend only
on the descending fixed weights and have strictly inward linear drift. -/
theorem baseline_weighted_upper_face (K r w z0 z1 : ℝ)
    (hK : 0≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (hz0 : |z0|≤(51/50)*K) (hz1 : |z1|≤(101/100)*K)
    (hw : |w|≤(38/15)*K) :
    (4-r/2)*z0+(3*r/2-12)*z1+(8-3*r/2)*K+r*w/16≤0 := by
  have h0 := abs_le.mp hz0
  have h1 := abs_le.mp hz1
  have hww := abs_le.mp hw
  have p0 := mul_nonneg (show 0≤r/2-4 by linarith) (show 0≤z0+(51/50)*K by linarith)
  have p1 := mul_nonneg (show 0≤3*r/2-12 by linarith) (show 0≤(101/100)*K-z1 by linarith)
  have pw := mul_nonneg (show 0≤r by linarith) (show 0≤(38/15)*K-w by linarith)
  have pr := mul_nonneg (show 0≤12-r by linarith) hK
  nlinarith

theorem baseline_weighted_lower_face (K r w z0 z1 : ℝ)
    (hK : 0≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (hz0 : |z0|≤(51/50)*K) (hz1 : |z1|≤(101/100)*K)
    (hw : |w|≤(38/15)*K) :
    0≤(4-r/2)*z0+(3*r/2-12)*z1-(8-3*r/2)*K+r*w/16 := by
  have h := baseline_weighted_upper_face K r (-w) (-z0) (-z1) hK hr0 hr1
    (by simpa using hz0) (by simpa using hz1) (by simpa using hw)
  linarith

/-- A larger independent mismatch box fails this exact weighted face test. -/
theorem weighted_budget_necessary (K W : ℝ)
    (h : (4-(12:ℝ)/2)*(-(51/50)*K)+((3:ℝ)*12/2-12)*((101/100)*K)+
      (8-(3:ℝ)*12/2)*K+12*W/16≤0) : W≤(38/15)*K := by linarith

theorem outer_cube_budget_necessary (R W : ℝ)
    (h : (-2)*(-R)+6*R-10*R+(3/4)*W≤0) : W≤(8/3)*R := by linarith

theorem fixed_clearance_numbers :
    (38/15:ℝ)*(9/200)=114/1000 ∧
    (9573033/100000000:ℝ)+(2221/40000)>3/20 ∧
    (9573033/100000000:ℝ)+(51/50)*(9/200)=14163033/100000000 := by norm_num

#print axioms general_gain_coordinate_identity
#print axioms general_gain_slope_identity
#print axioms baseline_weighted_upper_face
#print axioms baseline_weighted_lower_face
#print axioms weighted_budget_necessary
#print axioms outer_cube_budget_necessary
#print axioms fixed_clearance_numbers
end C04Faces
