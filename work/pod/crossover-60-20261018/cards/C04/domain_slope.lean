import Mathlib.Tactic
namespace C04Slope
/-- Same pending command as source. The lower position gain does not invalidate
the source-derived pending |v| and |a| bounds. -/
theorem pending_slope (v a r d : ℝ)
    (hv : |v|≤1533/50000) (ha : |a|≤33/25)
    (hr0 : 8≤r) (hr1 : r≤12) (hd : |d|≤1/100) :
    |-(16/3)*v-6*a-r*(-121/100+d-a)/2|≤8 := by
  have hv' := abs_le.mp hv
  have ha' := abs_le.mp ha
  have hd' := abs_le.mp hd
  have p0 := mul_nonneg (show 0≤6-r/2 by linarith) (show 0≤a+33/25 by linarith)
  have n0 := mul_nonneg (show 0≤6-r/2 by linarith) (show 0≤33/25-a by linarith)
  have p1 := mul_nonneg (show 0≤r by linarith) (show 0≤d+1/100 by linarith)
  have n1 := mul_nonneg (show 0≤r by linarith) (show 0≤1/100-d by linarith)
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Continuous rate interval, all signs of state and mismatch; L bounds just the
two exact endpoint expressions. This is not a sampled-rate assumption. -/
theorem digital_slope (K W L r z0 z1 z2 w : ℝ)
    (hK : 0≤K) (hr0 : 8≤r) (hr1 : r≤12)
    (h0 : |z0|≤(51/50)*K) (h1 : |z1|≤(101/100)*K)
    (h2 : |z2|≤K) (hw : |w|≤W)
    (h8 : (9736/75)*K+4*W≤L) (h12 : (8884/75)*K+6*W≤L) :
    |((8*r-224)/3)*z0+(512/3-12*r)*z1+(12*r-96)*z2-r*w/2|≤L := by
  have hz0 := abs_le.mp h0
  have hz1 := abs_le.mp h1
  have hz2 := abs_le.mp h2
  have hww := abs_le.mp hw
  have p0 := mul_nonneg (show 0≤(224-8*r)/3 by linarith) (show 0≤z0+(51/50)*K by linarith)
  have n0 := mul_nonneg (show 0≤(224-8*r)/3 by linarith) (show 0≤(51/50)*K-z0 by linarith)
  have p1 := mul_nonneg (show 0≤512/3-12*r by linarith) (show 0≤(101/100)*K-z1 by linarith)
  have n1 := mul_nonneg (show 0≤512/3-12*r by linarith) (show 0≤(101/100)*K+z1 by linarith)
  have p2 := mul_nonneg (show 0≤12*r-96 by linarith) (show 0≤K-z2 by linarith)
  have n2 := mul_nonneg (show 0≤12*r-96 by linarith) (show 0≤K+z2 by linarith)
  have p3 := mul_nonneg (show 0≤r by linarith) (show 0≤W+w by linarith)
  have n3 := mul_nonneg (show 0≤r by linarith) (show 0≤W-w by linarith)
  have p8 := mul_nonneg (show 0≤12-r by linarith) (show 0≤L-((9736/75)*K+4*W) by linarith)
  have p12 := mul_nonneg (show 0≤r-8 by linarith) (show 0≤L-((8884/75)*K+6*W) by linarith)
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

#print axioms pending_slope
#print axioms digital_slope
end C04Slope
