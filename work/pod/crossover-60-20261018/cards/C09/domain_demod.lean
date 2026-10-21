import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace C09Demod
/-- Constant relative detuning, nominal one-beat window. The integral-to-sinc
identity is a separate analytic bridge; this theorem checks the exact bound. -/
theorem sinc_leakage_bound (δ η : ℝ) (hη0 : 0≤η) (hη1 : η<1) (hδ : |δ|≤η) :
    |Real.sin (Real.pi*(1+δ))|/(Real.pi*(1+δ)) ≤ η/(1-η) := by
  have hd := abs_le.mp hδ
  have hp := Real.pi_pos
  have hden : 0<Real.pi*(1+δ) := mul_pos hp (by linarith)
  have hbase : 0<Real.pi*(1-η) := mul_pos hp (by linarith)
  have hs : |Real.sin (Real.pi*(1+δ))|=|Real.sin (Real.pi*δ)| := by
    rw [show Real.pi*(1+δ)=Real.pi*δ+Real.pi by ring,Real.sin_add_pi,abs_neg]
  have hnum : |Real.sin (Real.pi*(1+δ))|≤Real.pi*η := by
    rw [hs]
    calc
      _ ≤ |Real.pi*δ| := Real.abs_sin_le_abs
      _ = Real.pi*|δ| := by rw [abs_mul,abs_of_pos hp]
      _ ≤ Real.pi*η := mul_le_mul_of_nonneg_left hδ hp.le
  calc
    _ ≤ (Real.pi*η)/(Real.pi*(1+δ)) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (Real.pi*η)/(Real.pi*(1-η)) :=
      div_le_div_of_nonneg_left (mul_nonneg hp.le hη0) hbase (by nlinarith)
    _ = η/(1-η) := by field_simp

theorem one_percent_leakage (δ : ℝ) (hδ : |δ|≤1/100) :
    |Real.sin (Real.pi*(1+δ))|/(Real.pi*(1+δ))≤1/99 := by
  have h := sinc_leakage_bound δ (1/100) (by norm_num) (by norm_num) hδ
  norm_num at h ⊢
  exact h

#print axioms sinc_leakage_bound
#print axioms one_percent_leakage
end C09Demod
