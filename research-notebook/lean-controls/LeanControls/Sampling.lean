module

public import LeanControls.RobustPD

/-! A stronger common certificate, obtained with exact Bernstein coefficients.
All time units are normalized. This is a sufficient interval, not a maximal one.
-/
@[expose] public section
noncomputable section
namespace LeanControls.Sampling
open PD SampledPD

theorem half_step_decrease {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 2)
    (x v : ℝ) :
    energy (position h x v) (velocity h x v) - energy x v ≤
      -h * (x ^ 2 + v ^ 2) := by
  let N := x ^ 2 + v ^ 2
  let B0 := 4 * N
  let B1 := 5 * x ^ 2 + 3 / 2 * x * v + 19 / 6 * v ^ 2
  let B2 := 17 / 3 * x ^ 2 + 17 / 6 * x * v + 17 / 6 * v ^ 2
  let B3 := 43 / 8 * x ^ 2 + 17 / 8 * x * v + 51 / 32 * v ^ 2
  have b0 : N ≤ B0 := by dsimp [N, B0]; nlinarith [sq_nonneg x, sq_nonneg v]
  have b1 : N ≤ B1 := by dsimp [N, B1]; nlinarith [sq_nonneg (x + v), sq_nonneg x, sq_nonneg v]
  have b2 : N ≤ B2 := by dsimp [N, B2]; nlinarith [sq_nonneg (x + v), sq_nonneg x, sq_nonneg v]
  have b3 : N ≤ B3 := by dsimp [N, B3]; nlinarith [sq_nonneg (2 * x + v), sq_nonneg x, sq_nonneg v]
  have ht : 0 ≤ 1 - 2 * h := by linarith
  have p0 := mul_le_mul_of_nonneg_left b0 (pow_nonneg ht 3)
  have p1 := mul_le_mul_of_nonneg_left b1 (show 0 ≤ 6 * h * (1 - 2 * h) ^ 2 by positivity)
  have p2 := mul_le_mul_of_nonneg_left b2 (show 0 ≤ 12 * h ^ 2 * (1 - 2 * h) by positivity)
  have p3 := mul_le_mul_of_nonneg_left b3 (show 0 ≤ 8 * h ^ 3 by positivity)
  have bound : N ≤ (1 - 2 * h) ^ 3 * B0 + 6 * h * (1 - 2 * h) ^ 2 * B1 +
      12 * h ^ 2 * (1 - 2 * h) * B2 + 8 * h ^ 3 * B3 := by
    nlinarith only [p0, p1, p2, p3]
  have result := mul_le_mul_of_nonneg_left bound h0
  dsimp [N, B0, B1, B2, B3] at result
  unfold energy position velocity SampledPD.control
  nlinarith only [result]

theorem half_step_contract {h : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 2)
    (x v : ℝ) :
    energy (position h x v) (velocity h x v) ≤ (1 - h / 6) * energy x v := by
  have hd := half_step_decrease h0 hhi x v
  have hu := mul_le_mul_of_nonneg_left (energy_upper x v) h0
  nlinarith only [hd, hu]

theorem jitter_bound (h x v : ℕ → ℝ) {hmin : ℝ}
    (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 2)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 2)
    (hx : ∀ n, x (n + 1) = position (h n) (x n) (v n))
    (hv : ∀ n, v (n + 1) = velocity (h n) (x n) (v n)) (n : ℕ) :
    energy (x n) (v n) ≤ (1 - hmin / 6) ^ n * energy (x 0) (v 0) := by
  apply geometric_bound (V := fun k => energy (x k) (v k))
    (by linarith : 0 ≤ 1 - hmin / 6)
  intro k
  rw [hx k, hv k]
  exact (half_step_contract (hmin0.trans (hlo k)) (hhi k) _ _).trans
    (mul_le_mul_of_nonneg_right (by linarith [hlo k]) (energy_nonneg _ _))

theorem energy_add_bound (x v ex ev : ℝ) :
    energy (x + ex) (v + ev) ≤ 241 / 240 * energy x v + 241 * energy ex ev := by
  have hp := energy_nonneg (x - 240 * ex) (v - 240 * ev)
  unfold energy at *
  nlinarith only [hp]

theorem robust_step {h x v ex ev eps : ℝ} (hlo : 1 / 20 ≤ h) (hhi : h ≤ 1 / 2)
    (he : ex ^ 2 + ev ^ 2 ≤ eps ^ 2) :
    energy (position h x v + ex) (velocity h x v + ev) ≤
      239 / 240 * energy x v + 1446 * eps ^ 2 := by
  have hb := half_step_contract (by linarith : 0 ≤ h) hhi x v
  have hm := mul_le_mul_of_nonneg_right
    (show 1 - h / 6 ≤ 119 / 120 by linarith) (energy_nonneg x v)
  have ha := energy_add_bound (position h x v) (velocity h x v) ex ev
  have he' := energy_upper ex ev
  nlinarith only [hb, hm, ha, he', he, energy_nonneg x v]

end LeanControls.Sampling
