import Mathlib.Tactic
/-! Preserves the source weighted shrinking-envelope speed delta=3/1700.
This is a face certificate; a mixed-history execution bridge remains required. -/
namespace C04Shrink

theorem first_face (K z1 : ℝ) (hK : (9/200:ℝ)≤K)
    (hz1 : |z1|≤(101/100)*K) :
    4*(-((51/50)*K)+z1)≤-(51/50)*(3/1700) ∧
    (51/50)*(3/1700)≤4*((51/50)*K+z1) := by
  have h := abs_le.mp hz1
  constructor <;> linarith

theorem second_face (K z2 : ℝ) (hK : (9/200:ℝ)≤K)
    (hz2 : |z2|≤K) :
    4*(-((101/100)*K)+z2)≤-(101/100)*(3/1700) ∧
    (101/100)*(3/1700)≤4*((101/100)*K+z2) := by
  have h := abs_le.mp hz2
  constructor <;> linarith

/-- Stronger explicit margin than the required original shrinking speed. -/
theorem last_upper_margin (K r w z0 z1 : ℝ)
    (hK : (9/200:ℝ)≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (hz0 : |z0|≤(51/50)*K) (hz1 : |z1|≤(101/100)*K)
    (hw : |w|≤23/100) :
    (4-r/3)*z0+(3*r/2-12)*z1+(8-3*r/2)*K+r*w/16≤-19/5000 := by
  have h0 := abs_le.mp hz0
  have h1 := abs_le.mp hz1
  have hww := abs_le.mp hw
  have p0 := mul_nonneg (show 0≤4-r/3 by linarith) (show 0≤(51/50)*K-z0 by linarith)
  have p1 := mul_nonneg (show 0≤3*r/2-12 by linarith) (show 0≤(101/100)*K-z1 by linarith)
  have pw := mul_nonneg (show 0≤r by linarith) (show 0≤23/100-w by linarith)
  have pK := mul_nonneg (show 0≤1/25+13*r/40 by linarith) (show 0≤K-9/200 by linarith)
  nlinarith

theorem last_faces_shrink (K r w z0 z1 : ℝ)
    (hK : (9/200:ℝ)≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (hz0 : |z0|≤(51/50)*K) (hz1 : |z1|≤(101/100)*K)
    (hw : |w|≤23/100) :
    ((4-r/3)*z0+(3*r/2-12)*z1+(8-3*r/2)*K+r*w/16≤-3/1700) ∧
    (3/1700≤(4-r/3)*z0+(3*r/2-12)*z1-(8-3*r/2)*K+r*w/16) := by
  have hp := last_upper_margin K r w z0 z1 hK hr0 hr1 hz0 hz1 hw
  have hn := last_upper_margin K r (-w) (-z0) (-z1) hK hr0 hr1
    (by simpa using hz0) (by simpa using hz1) (by simpa using hw)
  constructor <;> linarith

#print axioms first_face
#print axioms second_face
#print axioms last_upper_margin
#print axioms last_faces_shrink
end C04Shrink
