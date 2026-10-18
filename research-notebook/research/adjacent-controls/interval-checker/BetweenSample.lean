module
public import LeanControls.UncertainLag
@[expose] public section
noncomputable section
namespace LeanControls.BetweenSample
open UncertainLag (State heldSolution polynomialHeld)

/-- A post-clamp command error is included explicitly. No bound on the
pre-clamp request is needed to bound the saturated part. -/
theorem command_abs_bound (request : ℝ) {d D : ℝ} (hd : |d| ≤ D) :
    |RobustPD.saturate 1 request+d| ≤ 1+D := by
  exact (abs_add_le _ _).trans (add_le_add
    (SaturationSector.clamp_abs_le (by norm_num) request) hd)

/-- A whole-hold position bound for a bounded command and bounded initial
coordinates. The exact exponential is enclosed once for every elapsed time.
The command remains held; the rate is positive and r*s<=1. -/
theorem position_bound {r s u X V A U : ℝ} {z : State}
    (hr : 0 < r) (hs : 0 ≤ s) (hrs : r*s ≤ 1)
    (hx : |z 0| ≤ X) (hv : |z 1| ≤ V) (ha : |z 2| ≤ A) (hu : |u| ≤ U) :
    |heldSolution r s u z 0| ≤ X+s*V+U*s^2/2+(A+U)*s^2 := by
  obtain ⟨theta,ht0,ht1,heq⟩ := UncertainLag.held_polynomial_enclosure hr hs hrs
  rw [heq]
  have ht : |theta| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hd : |z 2-u| ≤ A+U := (abs_sub _ _).trans (add_le_add ha hu)
  have hAU : 0 ≤ A+U := (abs_nonneg _).trans hd
  have hvel : |s*z 1| ≤ s*V := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hv hs
  have hcmd : |u*s^2/2| ≤ U*s^2/2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg s)]
    norm_num
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu (sq_nonneg s)) (by norm_num)
  have hrem : |(z 2-u)*theta*s^2| ≤ (A+U)*s^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s)]
    have hm := mul_le_mul hd ht (abs_nonneg theta) hAU
    simpa using mul_le_mul_of_nonneg_right hm (sq_nonneg s)
  dsimp [polynomialHeld]
  have h1 := abs_add_le (z 0) (s*z 1)
  have h2 := abs_add_le (z 0+s*z 1) (u*s^2/2)
  have h3 := abs_add_le (z 0+s*z 1+u*s^2/2) ((z 2-u)*theta*s^2)
  linarith

/-- A convenient coarse envelope for one 0.05 hold. This does not assume that
the endpoint certificate bounds the intermediate trajectory. -/
theorem short_hold_safe {r s u : ℝ} {z : State}
    (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s ≤ 1/20) (hrs : r*s ≤ 1)
    (hx : |z 0| ≤ 3/2) (hv : |z 1| ≤ 1) (ha : |z 2| ≤ 1) (hu : |u| ≤ 1) :
    |heldSolution r s u z 0| ≤ 2 := by
  have hb := position_bound hr hs0 hrs hx hv ha hu
  have hs2 : s^2 ≤ (1/20:ℝ)^2 := by nlinarith
  nlinarith

end LeanControls.BetweenSample
#print axioms LeanControls.BetweenSample.command_abs_bound
#print axioms LeanControls.BetweenSample.position_bound
#print axioms LeanControls.BetweenSample.short_hold_safe
