import Mathlib.Tactic
namespace C04Codesign
/-- The retuned law changes only position gain 8 to16/3, retaining coordinates,
weights, fixed center, sensors, startup command and authority. -/
theorem weighted_upper_face (K r w z0 z1 : ℝ)
    (hK : 0≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (hz0 : |z0|≤(51/50)*K) (hz1 : |z1|≤(101/100)*K)
    (hw : |w|≤(394/75)*K) :
    (4-r/3)*z0+(3*r/2-12)*z1+(8-3*r/2)*K+r*w/16≤0 := by
  have h0 := abs_le.mp hz0
  have h1 := abs_le.mp hz1
  have hww := abs_le.mp hw
  have p0 := mul_nonneg (show 0≤4-r/3 by linarith) (show 0≤(51/50)*K-z0 by linarith)
  have p1 := mul_nonneg (show 0≤3*r/2-12 by linarith) (show 0≤(101/100)*K-z1 by linarith)
  have pw := mul_nonneg (show 0≤r by linarith) (show 0≤(394/75)*K-w by linarith)
  have pr := mul_nonneg (show 0≤12-r by linarith) hK
  nlinarith

theorem weighted_lower_face (K r w z0 z1 : ℝ)
    (hK : 0≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (hz0 : |z0|≤(51/50)*K) (hz1 : |z1|≤(101/100)*K)
    (hw : |w|≤(394/75)*K) :
    0≤(4-r/3)*z0+(3*r/2-12)*z1-(8-3*r/2)*K+r*w/16 := by
  have h := weighted_upper_face K r (-w) (-z0) (-z1) hK hr0 hr1
    (by simpa using hz0) (by simpa using hz1) (by simpa using hw)
  linarith

theorem weighted_budget_necessary (K W : ℝ)
    (h : 6*((101/100)*K)-10*K+(3/4)*W≤0) : W≤(394/75)*K := by linarith

theorem slope_endpoints (K W : ℝ) :
    (160/3)*(51/50)*K+(224/3)*(101/100)*K+4*W=(9736/75)*K+4*W ∧
    (128/3)*(51/50)*K+(80/3)*(101/100)*K+48*K+6*W=(8884/75)*K+6*W := by constructor <;> ring

theorem command_and_measurement (K : ℝ) :
    (32/3)*(51/50)*K+8*(101/100)*K+8*K=(674/25)*K ∧
    (16/3:ℝ)*(1/1000)+6*(1/100)+(1/2)*(1/20)+(1/100)=301/3000 := by constructor <;> ring

theorem candidate_budget : (394/75:ℝ)*(9/200)=591/2500 ∧
    (234/1000:ℝ)<591/2500 := by norm_num

#print axioms weighted_upper_face
#print axioms weighted_lower_face
#print axioms weighted_budget_necessary
#print axioms slope_endpoints
#print axioms command_and_measurement
#print axioms candidate_budget
end C04Codesign
