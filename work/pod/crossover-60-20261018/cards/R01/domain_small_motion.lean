import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace R01TubeLimit

/- Countermodel to an inference from a position tube alone. This is NOT an ODE
   trajectory construction and does not refute the original plant theorem. -/
theorem constant_hold_inside_small_move_tube
    (delta R u : ℝ) (hd : 0 ≤ delta) (hdr : delta ≤ R)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : |0 - delta * u| ≤ R := by
  have hp : 0 ≤ delta * u := mul_nonneg hd hu
  have hpr : delta * u ≤ delta := by nlinarith
  rw [zero_sub, abs_neg, abs_of_nonneg hp]
  exact le_trans hpr hdr

theorem tenth_mm_hold_fits_two_tenths_tube (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    |(0 : ℝ) - (1 / 10000) * u| ≤ 1 / 5000 ∧ ¬ (0 : ℝ) < 0 := by
  constructor
  · exact constant_hold_inside_small_move_tube _ _ u (by norm_num) (by norm_num) hu hu1
  · exact lt_irrefl _

#print axioms constant_hold_inside_small_move_tube
#print axioms tenth_mm_hold_fits_two_tenths_tube
end R01TubeLimit
