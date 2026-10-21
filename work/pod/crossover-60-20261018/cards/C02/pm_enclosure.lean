import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace C02Enclosure
-- Conditional error-budget transfer; the numerical trajectories are not thereby enclosed.
theorem basis_error (a b A B c ea eb : ℝ)
    (ha : |a-A| ≤ ea) (hb : |b-B| ≤ eb) :
    |(a+c*b)-(A+c*B)| ≤ ea+|c| * eb := by
  calc
    |(a+c*b)-(A+c*B)| = |(a-A)+c*(b-B)| := by congr 1; ring
    _ ≤ |a-A|+|c*(b-B)| := abs_add_le _ _
    _ = |a-A|+|c| * |b-B| := by rw [abs_mul]
    _ ≤ ea+|c| * eb := add_le_add ha (mul_le_mul_of_nonneg_left hb (abs_nonneg _))

theorem uniform_objective_regret (F G : ℝ → ℝ) (chosen competitor eps : ℝ)
    (hc : |F chosen-G chosen| ≤ eps)
    (ho : |F competitor-G competitor| ≤ eps)
    (opt : G chosen ≤ G competitor) :
    F chosen ≤ F competitor+2*eps := by
  have hc1 := (abs_le.mp hc).2
  have ho1 := (abs_le.mp ho).1
  linarith
#print axioms basis_error
#print axioms uniform_objective_regret
theorem approximate_objective_regret (F G : ℝ → ℝ) (chosen competitor eps eta : ℝ)
    (hc : |F chosen-G chosen| ≤ eps)
    (ho : |F competitor-G competitor| ≤ eps)
    (opt : G chosen ≤ G competitor+eta) :
    F chosen ≤ F competitor+2*eps+eta := by
  have hc1 := (abs_le.mp hc).2
  have ho1 := (abs_le.mp ho).1
  linarith
#print axioms approximate_objective_regret
end C02Enclosure
