import Mathlib

/-!
# Bode (1945) sensitivity integral, discrete time, via Jensen's formula

Discrete-time Bode integral (Sung–Hara 1988, Mohtadi 1990): for a stable closed loop whose
loop gain is strictly proper, `(1/2π) ∫_{-π}^{π} log |S(e^{iθ})| dθ = Σ log |pᵢ|` over unstable
open-loop poles `pᵢ`. In particular it is `≥ 0`: the waterbed effect.

* `bode_jensen` / `bode_waterbed_nonneg` / `bode_zero_of_no_zeros`: general form, with `S` written
  in the variable `w = z⁻¹` (so the closed unit disk in `w` is the exterior of the unit disk
  in `z`, `S(w = 0) = S(z = ∞) = 1` by strict properness, and zeros of `S` in the disk are the
  unstable open-loop poles).
* `bode_first_order`: fully explicit for plant `1/(z - p)` with proportional gain `k`:
  `S(z) = (z - p)/(z - (p - k))`, average of `log |S|` on the unit circle is `log⁺ |p|`.
-/

open Real Metric

namespace ClassicsFrequency

/-- **Discrete Bode integral (Jensen form).** -/
theorem bode_jensen {S : ℂ → ℂ} (hS : AnalyticOnNhd ℂ S (closedBall 0 1)) (h0 : S 0 = 1) :
    circleAverage (fun w => log ‖S w‖) 0 1 =
      ∑ᶠ u, (MeromorphicOn.divisor S (closedBall 0 1) u : ℝ) * log ‖u‖⁻¹ := by
  have := (show AnalyticOnNhd ℂ S (closedBall 0 |1|) by rwa [abs_one]).circleAverage_log_norm
    (c := 0) one_ne_zero (by rw [h0]; exact one_ne_zero)
  rw [abs_one] at this
  simpa [h0] using this

/-- **Waterbed effect**: the average of `log |S|` over the unit circle is nonnegative. -/
theorem bode_waterbed_nonneg {S : ℂ → ℂ} (hS : AnalyticOnNhd ℂ S (closedBall 0 1))
    (h0 : S 0 = 1) : 0 ≤ circleAverage (fun w => log ‖S w‖) 0 1 := by
  rw [bode_jensen hS h0]
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall (0 : ℂ) 1
  · apply mul_nonneg
    · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hS u
    · rcases eq_or_ne u 0 with rfl | hu0
      · simp
      · apply log_nonneg
        rw [mem_closedBall, dist_zero_right] at hu
        exact one_le_inv₀ (norm_pos_iff.2 hu0) |>.2 hu
  · simp [(MeromorphicOn.divisor S (closedBall 0 1)).apply_eq_zero_of_notMem hu]

/-- **Bode's sensitivity integral (open-loop stable case)**: if `S` has no zeros in the disk
(no unstable open-loop poles), the average of `log |S|` is exactly `0`. -/
theorem bode_zero_of_no_zeros {S : ℂ → ℂ} (hS : AnalyticOnNhd ℂ S (closedBall 0 1))
    (h0 : S 0 = 1) (hnz : ∀ w ∈ closedBall (0 : ℂ) 1, S w ≠ 0) :
    circleAverage (fun w => log ‖S w‖) 0 1 = 0 := by
  rw [bode_jensen hS h0]
  apply finsum_eq_zero_of_forall_eq_zero
  intro u
  by_cases hu : u ∈ closedBall (0 : ℂ) 1
  · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hS hu, (analyticOrderAt_eq_zero.2 (Or.inr (hnz u hu)))]
    simp
  · simp [(MeromorphicOn.divisor S (closedBall 0 1)).apply_eq_zero_of_notMem hu]

/-- **Concrete discrete Bode integral.** Plant `P(z) = 1/(z - p)`, controller gain `k`,
closed-loop pole `q = p - k` strictly inside the unit circle, open-loop pole off the circle.
Then the average of `log |S(e^{iθ})|` equals `log⁺ |p|`: zero for a stable plant, `log |p|`
for an unstable one. -/
theorem bode_first_order (p k : ℂ) (hq : ‖p - k‖ < 1) (hp : ‖p‖ ≠ 1) :
    circleAverage (fun z => log ‖(z - p) / (z - (p - k))‖) 0 1 = log⁺ ‖p‖ := by
  have hcongr : circleAverage (fun z => log ‖(z - p) / (z - (p - k))‖) 0 1 =
      circleAverage ((fun z => log ‖z - p‖) - fun z => log ‖z - (p - k)‖) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    rw [abs_one, mem_sphere, dist_zero_right] at hz
    have h1 : z - p ≠ 0 := fun h => hp (by rw [← sub_eq_zero.1 h, hz])
    have h2 : z - (p - k) ≠ 0 := fun h => by
      rw [← sub_eq_zero.1 h, hz] at hq; exact lt_irrefl _ hq
    simp [log_div (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)]
  rw [hcongr, circleAverage_sub (circleIntegrable_log_norm_sub_const 1)
    (circleIntegrable_log_norm_sub_const 1), circleAverage_log_norm_sub_const_eq_posLog,
    circleAverage_log_norm_sub_const_eq_posLog]
  have : log⁺ ‖p - k‖ = 0 := (posLog_eq_zero_iff _).2 (by
    rw [abs_of_nonneg (norm_nonneg _)]; exact hq.le)
  rw [this, sub_zero]

end ClassicsFrequency
