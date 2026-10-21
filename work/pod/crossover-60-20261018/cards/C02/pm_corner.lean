import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace C02Corner
-- Pointwise Hamiltonian algebra only. No trajectory existence or optimal-control theorem.
theorem interval_rate_max (r lo hi A : ℝ) (hl : lo ≤ r) (hh : r ≤ hi) :
    r*A ≤ max (lo*A) (hi*A) := by
  by_cases hA : 0 ≤ A
  · exact le_trans (mul_le_mul_of_nonneg_right hh hA) (le_max_right _ _)
  · have hn : A ≤ 0 := le_of_not_ge hA
    exact le_trans (mul_le_mul_of_nonpos_right hl hn) (le_max_left _ _)

theorem bounded_disturbance (r lambda z w W : ℝ) (hr : 0 ≤ r)
    (hw : |w| ≤ W) : lambda*r*(z+w) ≤ r*(lambda*z+|lambda| * W) := by
  have hprod : lambda*w ≤ |lambda| * W := by
    calc
      lambda*w ≤ |lambda*w| := le_abs_self _
      _ = |lambda| * |w| := abs_mul _ _
      _ ≤ |lambda| * W := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hprod hr
  nlinarith

#print axioms interval_rate_max
#print axioms bounded_disturbance
end C02Corner
