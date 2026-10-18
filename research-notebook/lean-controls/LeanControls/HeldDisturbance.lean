module

public import LeanControls.Trajectories

/-!
# From held acceleration disturbance to the sample-boundary error budget

This covers a disturbance constant on each interval. Arbitrarily time-varying
measurable disturbances require a separate integral estimate.
-/

@[expose] public section
noncomputable section

namespace LeanControls.HeldDisturbance

open PD SampledPD RobustPD

/-- Integration of a constant acceleration error gives these two state errors. -/
theorem error_budget {h d D : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 6)
    (hd : |d| ≤ D) : (h ^ 2 / 2 * d) ^ 2 + (h * d) ^ 2 ≤ (D / 5) ^ 2 := by
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hd2 : d ^ 2 ≤ D ^ 2 := by nlinarith [abs_le.mp hd]
  have h2 : h ^ 2 ≤ 1 / 36 := by nlinarith
  have h4 : h ^ 4 ≤ 1 / 1296 := by nlinarith [sq_nonneg (h ^ 2 - 1 / 36)]
  have hc : h ^ 4 / 4 + h ^ 2 ≤ 1 / 25 := by linarith
  have hp := mul_le_mul_of_nonneg_right hc (sq_nonneg d)
  nlinarith only [hp, hd2]

/-- A concrete acceleration-disturbance bound feeds the established safety theorem. -/
theorem demo_safe_acceleration (h d : ℕ → ℝ)
    (hlo : ∀ n, 1 / 20 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (hd : ∀ n, |d n| ≤ 1 / 200) :
    ∀ n, let z := run h (fun k => h k ^ 2 / 2 * d k) (fun k => h k * d k) 1 (1 / 10, 0) n
      energy z.1 z.2 ≤ 1 / 10 ∧ |SampledPD.control z.1 z.2| ≤ 1 := by
  apply demo_safe h _ _ hlo hhi
  intro n
  have he := error_budget (by linarith [hlo n] : 0 ≤ h n) (hhi n) (hd n)
  norm_num at he
  norm_num
  exact he

/-- An explicit between-sample energy envelope for the perturbed segment. -/
theorem intersample_bound {t x v d : ℝ} (ht : 0 ≤ t) (thi : t ≤ 1 / 6)
    (hE : energy x v ≤ 1 / 10) (hd : |d| ≤ 1 / 200) :
    energy (position t x v + t ^ 2 / 2 * d) (velocity t x v + t * d) ≤ 103 / 1000 := by
  have herr := error_budget ht thi hd
  have hsmall := energy_upper (t ^ 2 / 2 * d) (t * d)
  have hnom := intersample_energy ht (le_refl t) thi (x := x) (v := v)
  have hadd := energy_add_bound (position t x v) (velocity t x v) (t ^ 2 / 2 * d) (t * d)
  norm_num at herr
  linarith

end LeanControls.HeldDisturbance
