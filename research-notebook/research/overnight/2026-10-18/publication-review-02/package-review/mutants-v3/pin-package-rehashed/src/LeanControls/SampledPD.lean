module

public import LeanControls.PD
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Exact held-input PD sampling

For ẋ = v and v̇ = u, hold u = -2x₀ - 3v₀ during each sample interval.
The polynomial segment is an exact solution of those differential equations.
This file proves a common quadratic certificate for all h in [0, 1/6].
State and time are normalized; no physical unit calibration is asserted.
-/

@[expose] public section

noncomputable section

namespace LeanControls.SampledPD

open PD

def control (x v : ℝ) : ℝ := -2 * x - 3 * v
def position (t x v : ℝ) : ℝ := x + t * v + t ^ 2 / 2 * control x v
def velocity (t x v : ℝ) : ℝ := v + t * control x v

theorem position_initial (x v : ℝ) : position 0 x v = x := by simp [position]
theorem velocity_initial (x v : ℝ) : velocity 0 x v = v := by simp [velocity]

/-- Exact segment dynamics: derivative of position is velocity. -/
theorem position_derivative (t x v : ℝ) :
    HasDerivAt (fun s => position s x v) (velocity t x v) t := by
  convert (((hasDerivAt_id t).mul_const v).const_add x).add
    ((((hasDerivAt_id t).pow 2).div_const 2).mul_const (control x v)) using 1
  · ext s
    simp [position]
  · simp [velocity]

/-- Exact segment dynamics: acceleration equals the sampled, held control. -/
theorem velocity_derivative (t x v : ℝ) :
    HasDerivAt (fun s => velocity s x v) (control x v) t := by
  simpa [velocity] using ((hasDerivAt_id t).mul_const (control x v)).const_add v

theorem energy_identity (h x v : ℝ) :
    energy (position h x v) (velocity h x v) - energy x v =
      -4 * h * (x ^ 2 + v ^ 2) +
      h ^ 2 * (-6 * x ^ 2 - 9 * x * v + 5 * v ^ 2) +
      h ^ 3 * (4 * x ^ 2 + 2 * x * v - 6 * v ^ 2) +
      h ^ 4 * (5 * x ^ 2 + 15 * x * v + 45 / 4 * v ^ 2) := by
  unfold energy position velocity control
  ring

theorem energy_decrease {h : ℝ} (h0 : 0 ≤ h) (hmax : h ≤ 1 / 6) (x v : ℝ) :
    energy (position h x v) (velocity h x v) - energy x v ≤
      -2 * h * (x ^ 2 + v ^ 2) := by
  rw [energy_identity]
  have hs : 0 ≤ x ^ 2 + v ^ 2 := by positivity
  have hb2 : -6 * x ^ 2 - 9 * x * v + 5 * v ^ 2 ≤ 10 * (x ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (x + v), sq_nonneg x, sq_nonneg v]
  have hb3 : 4 * x ^ 2 + 2 * x * v - 6 * v ^ 2 ≤ 5 * (x ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (x - v), sq_nonneg v]
  have hb4 : 5 * x ^ 2 + 15 * x * v + 45 / 4 * v ^ 2 ≤ 19 * (x ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (x - v), sq_nonneg x, sq_nonneg v]
  have h2 : h ^ 2 ≤ h / 6 := by nlinarith
  have h3 : h ^ 3 ≤ h / 36 := by
    have hh := mul_le_mul_of_nonneg_left h2 h0
    nlinarith only [hh, h2]
  have h4 : h ^ 4 ≤ h / 216 := by
    have hh := mul_le_mul_of_nonneg_left h3 h0
    nlinarith only [hh, h2]
  have hc : 10 * h ^ 2 + 5 * h ^ 3 + 19 * h ^ 4 ≤ 2 * h := by
    linarith
  have hprod2 := mul_le_mul_of_nonneg_left hb2 (pow_nonneg h0 2)
  have hprod3 := mul_le_mul_of_nonneg_left hb3 (pow_nonneg h0 3)
  have hprod4 := mul_le_mul_of_nonneg_left hb4 (pow_nonneg h0 4)
  have hprod := mul_le_mul_of_nonneg_right hc hs
  nlinarith only [hprod2, hprod3, hprod4, hprod]

theorem energy_contract {h : ℝ} (h0 : 0 ≤ h) (hmax : h ≤ 1 / 6) (x v : ℝ) :
    energy (position h x v) (velocity h x v) ≤ (1 - h / 3) * energy x v := by
  have hd := energy_decrease h0 hmax x v
  have hu := mul_le_mul_of_nonneg_left (energy_upper x v) h0
  nlinarith only [hd, hu]

/-- Jitter may be adversarial, provided every interval meets these bounds. -/
theorem jitter_energy_bound (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminmax : hmin ≤ 1 / 6)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 6)
    (hx : ∀ n, x (n + 1) = position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = velocity (h n) (x n) (v n)) (n : ℕ) :
    energy (x n) (v n) ≤ (1 - hmin / 3) ^ n * energy (x 0) (v 0) := by
  apply geometric_bound (V := fun k => energy (x k) (v k))
    (by linarith : 0 ≤ 1 - hmin / 3)
  intro k
  rw [hx k, hv k]
  exact (energy_contract (hmin0.trans (hlo k)) (hhi k) _ _).trans
    (mul_le_mul_of_nonneg_right (by linarith [hlo k]) (energy_nonneg _ _))

/-- The same certificate decreases between samples, not just at sample instants. -/
theorem intersample_energy {h t x v : ℝ} (ht : 0 ≤ t) (hth : t ≤ h)
    (hmax : h ≤ 1 / 6) : energy (position t x v) (velocity t x v) ≤ energy x v := by
  have hd := energy_decrease ht (hth.trans hmax) x v
  have hn : 0 ≤ 2 * t * (x ^ 2 + v ^ 2) := by positivity
  linarith

end LeanControls.SampledPD
