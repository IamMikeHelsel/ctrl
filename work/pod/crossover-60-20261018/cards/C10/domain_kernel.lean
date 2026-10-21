import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace C10

theorem polynomial_exp_bound (x : ℝ) (hx : 0 ≤ x) :
    |1 - 2*x + x^2/2| ≤ Real.exp x := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x - 1/2)]
  · nlinarith

theorem impulse_second_derivative_bound (t : ℝ) (ht : 0 ≤ t) :
    |(1 - 8*t + 8*t^2) * Real.exp (-4*t)| ≤ 1 := by
  have h := polynomial_exp_bound (4*t) (by positivity)
  have hid : 1 - 2*(4*t) + (4*t)^2/2 = 1 - 8*t + 8*t^2 := by ring
  have hp : |1 - 8*t + 8*t^2| ≤ Real.exp (4*t) := by rwa [hid] at h
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (4*t) * Real.exp (-4*t) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

theorem short_reference_velocities_nonnegative (h s J : ℝ)
    (hh : 0 ≤ h) (hs : 0 ≤ s) (hsh : s ≤ h) (hJ : 0 ≤ J) :
    0 ≤ J*s^2/2 ∧
    0 ≤ J*(h^2/2+h*s-s^2/2) ∧
    0 ≤ J*(h^2-s^2/2) ∧
    0 ≤ J*(h-s)^2/2 := by
  have hsq : s^2 ≤ h^2 := by nlinarith
  have hhs : 0 ≤ h*s := mul_nonneg hh hs
  refine ⟨by positivity, ?_, ?_, by positivity⟩
  · apply mul_nonneg hJ; nlinarith
  · apply mul_nonneg hJ; nlinarith

-- Exact integrals of the four displayed polynomial velocity pieces.
theorem short_reference_total_travel (J h : ℝ) :
    J*h^3/6 + J*(h^3/2+h^3/2-h^3/6) +
    J*(h^3-h^3/6) + J*h^3/6 = 2*J*h^3 := by ring

theorem midpoint_travel_budget :
    |8*(5/48 : ℝ)-1| * (1/6250) + (1/2000)/8 = 107/1200000 ∧
    (107/1200000 : ℝ) < 1/5000 := by norm_num

theorem nominal_travel_budget :
    |8*(1/10 : ℝ)-1| * (1/6250) + (1/2000)/8 = 189/2000000 ∧
    (189/2000000 : ℝ) < 1/5000 := by norm_num

#print axioms polynomial_exp_bound
#print axioms impulse_second_derivative_bound
#print axioms short_reference_velocities_nonnegative
#print axioms short_reference_total_travel
#print axioms midpoint_travel_budget
#print axioms nominal_travel_budget
end C10
