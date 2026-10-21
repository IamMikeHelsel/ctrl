import Mathlib.Tactic
namespace C11Faces
-- Source z3=x-c+v/2+a/16, under the actual pending command.
theorem lower_attained_sensor_facet (mx v a : ℝ) (hf : 8*v+a= -928/625) :
    (mx-1/1000)-(mx+v/4+a/32)+(v-1/100)/2+(a-1/20)/16 =
      -(2221/40000) := by linarith

-- One legal rate/disturbance suffices to refute universal delayed admission.
theorem lower_facet_outward (v a : ℝ) (hf : 8*v+a= -928/625)
    (ha : |a|≤2081/1250) :
    (v-1/100)+(a-1/20)/2+8*(-121/100-(a-1/20))/16 ≤ -237/400 := by
  have hh := abs_le.mp ha
  linarith

-- In contrast, the attained upper sensor corner points strictly inward.
theorem upper_facet_inward (v a r d : ℝ) (hf : 8*v+a=928/625)
    (ha : |a|≤2081/1250) (hr : 8≤r ∧ r≤12) (hd : |d|≤1/100) :
    (v+1/100)+(a+1/20)/2+r*(-121/100+d-(a+1/20))/16 ≤ -463/5000 := by
  have hab := abs_le.mp ha
  have hdb := abs_le.mp hd
  have hp := mul_nonneg (show 0≤r-6 by linarith) (show 0≤a+2081/1250 by linarith)
  have hpd := mul_nonneg (show 0≤r by linarith) (show 0≤1/100-d by linarith)
  nlinarith
end C11Faces
#print axioms C11Faces.lower_attained_sensor_facet
#print axioms C11Faces.lower_facet_outward
#print axioms C11Faces.upper_facet_inward
