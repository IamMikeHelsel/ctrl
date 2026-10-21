import Mathlib.Tactic
namespace R03ClockBudget

-- Algebraic consequence of chain-rule formulas, not a proof of differentiability or clock fidelity.
theorem velocity_bound {v c1 V s : ℝ}
    (hv : |v|≤V) (hc : |c1|≤s) (hV : 0≤V) : |v*c1|≤V*s := by
  rw [abs_mul]
  exact mul_le_mul hv hc (abs_nonneg c1) hV

theorem acceleration_bound {v a c1 c2 V A s r : ℝ}
    (hv : |v|≤V) (ha : |a|≤A) (h1 : |c1|≤s) (h2 : |c2|≤r)
    (hV : 0≤V) (hA : 0≤A) (hs : 0≤s) :
    |a*c1^2+v*c2|≤A*s^2+V*r := by
  have hsq : |c1^2|≤s^2 := by rw [abs_pow]; nlinarith [abs_nonneg c1]
  have hp1 : |a*c1^2|≤A*s^2 := by rw [abs_mul]; exact mul_le_mul ha hsq (abs_nonneg _) hA
  have hp2 : |v*c2|≤V*r := by rw [abs_mul]; exact mul_le_mul hv h2 (abs_nonneg _) hV
  have hh := abs_add_le (a*c1^2) (v*c2)
  linarith

theorem jerk_bound {v a j c1 c2 c3 V A J s r k : ℝ}
    (hv : |v|≤V) (ha : |a|≤A) (hj : |j|≤J)
    (h1 : |c1|≤s) (h2 : |c2|≤r) (h3 : |c3|≤k)
    (hV : 0≤V) (hA : 0≤A) (hJ : 0≤J) (hs : 0≤s) (hr : 0≤r) :
    |j*c1^3+3*a*c1*c2+v*c3|≤J*s^3+3*A*s*r+V*k := by
  have hsq : |c1|^2≤s^2 := by nlinarith [abs_nonneg c1]
  have hcube : |c1^3|≤s^3 := by
    rw [abs_pow]
    have hh := mul_le_mul hsq h1 (abs_nonneg c1) (sq_nonneg s)
    nlinarith only [hh]
  have hp1 : |j*c1^3|≤J*s^3 := by rw [abs_mul]; exact mul_le_mul hj hcube (abs_nonneg _) hJ
  have ha1 : |a*c1|≤A*s := by rw [abs_mul]; exact mul_le_mul ha h1 (abs_nonneg _) hA
  have ha2 : |(a*c1)*c2|≤A*s*r := by rw [abs_mul]; exact mul_le_mul ha1 h2 (abs_nonneg _) (mul_nonneg hA hs)
  have hp2 : |3*a*c1*c2|≤3*A*s*r := by
    have hid : 3*a*c1*c2=3*((a*c1)*c2) := by ring
    rw [hid,abs_mul]
    norm_num
    nlinarith only [ha2]
  have hp3 : |v*c3|≤V*k := by rw [abs_mul]; exact mul_le_mul hv h3 (abs_nonneg _) hV
  have hh := abs_add_le (j*c1^3+3*a*c1*c2) (v*c3)
  have hh2 := abs_add_le (j*c1^3) (3*a*c1*c2)
  linarith

#print axioms velocity_bound
#print axioms acceleration_bound
#print axioms jerk_bound
end R03ClockBudget
