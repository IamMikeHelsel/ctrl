import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith


set_option autoImplicit false
namespace M01Quotient

/-- Explicit algebraic lifting of an affine quotient-curve point. This only
 supplies the first two nonzero-row constraints; three other rows remain. -/
theorem doubling_first_constraint (x y a b : ℚ) (hy : y ≠ 0)
    (hcurve : y^2 = x * (x+a) * (x+b)) :
    ((x^2 + 2*a*x + a*b) / (2*y))^2 =
      ((x^2 - a*b) / (2*y))^2 + a := by
  have hp : (x^2+2*a*x+a*b)^2 - (x^2-a*b)^2 =
      4*a*(x*(x+a)*(x+b)) := by ring
  rw [← hcurve] at hp
  field_simp
  nlinarith [hp]

theorem doubling_second_constraint (x y a b : ℚ) (hy : y ≠ 0)
    (hcurve : y^2 = x * (x+a) * (x+b)) :
    ((x^2 + 2*b*x + a*b) / (2*y))^2 =
      ((x^2 - a*b) / (2*y))^2 + b := by
  have hs : y^2 = x * (x+b) * (x+a) := by rw [hcurve]; ring
  simpa [mul_comm a b] using doubling_first_constraint x y b a hy hs

#print axioms doubling_first_constraint
#print axioms doubling_second_constraint
end M01Quotient
