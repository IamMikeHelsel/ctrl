import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith


set_option autoImplicit false
namespace C02AffineObjective

/-- Completing the square for a finite-horizon squared position error functional.
 A=integral b², B=integral a*b, C=integral a². Integral and ODE binding are separate. -/
theorem quadratic_objective_identity (A B C k : ℝ) (hA : A ≠ 0) :
    A*k^2 + 2*B*k + C - (C-B^2/A) = A*(k+B/A)^2 := by
  field_simp
  ring

theorem quadratic_objective_optimal (A B C k : ℝ) (hA : 0 < A) :
    C-B^2/A ≤ A*k^2+2*B*k+C := by
  have hi := quadratic_objective_identity A B C k (ne_of_gt hA)
  have hn : 0 ≤ A*(k+B/A)^2 := mul_nonneg (le_of_lt hA) (sq_nonneg _)
  linarith

/-- Algebraic residual check: the reciprocal known rate cancels planned jerk. -/
theorem reciprocal_rate_zero_residual (r j : ℝ) (hr : r ≠ 0) :
    (r*(1/r)-1)*j=0  := by field_simp; ring

#print axioms quadratic_objective_identity
#print axioms quadratic_objective_optimal
#print axioms reciprocal_rate_zero_residual
end C02AffineObjective
