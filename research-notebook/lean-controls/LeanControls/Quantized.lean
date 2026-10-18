module
public import LeanControls.Sampling
public import Mathlib.Algebra.Order.Round
@[expose] public section
noncomputable section
namespace LeanControls.Quantized
open PD SampledPD RobustPD

/-- Ideal nearest-grid rounding over mathematical reals, not machine floating point. -/
def quantize (delta x : ℝ) : ℝ := delta * (round (x / delta) : ℤ)

theorem rounding_error {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    |quantize delta x - x| ≤ delta / 2 := by
  have hr := abs_sub_round (x / delta)
  have hm := mul_le_mul_of_nonneg_left hr hd.le
  have hid : quantize delta x - x = delta * ((round (x / delta) : ℤ) - x / delta) := by
    unfold quantize
    field_simp
  rw [hid, abs_mul, abs_of_pos hd, abs_sub_comm]
  linarith

/-- Clipping cannot increase the error relative to an in-range nominal input. -/
theorem clipping_error {U u e : ℝ} (hu : |u| ≤ U) :
    |saturate U (u + e) - u| ≤ |e| := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hu
  unfold saturate
  apply abs_le.mpr
  constructor <;> rcases le_total (u + e) U with hc | hc
  · rw [min_eq_right hc]
    exact le_trans (by linarith [le_abs_self (-e), neg_le_abs e])
      (sub_le_sub_right (le_max_right (-U) (u + e)) u)
  · rw [min_eq_left hc, max_eq_right (by linarith : -U ≤ U)]
    linarith [abs_nonneg e]
  · rw [min_eq_right hc]
    apply (sub_le_iff_le_add).mpr
    exact max_le (by linarith [abs_nonneg e]) (by linarith [le_abs_self e])
  · rw [min_eq_left hc, max_eq_right (by linarith : -U ≤ U)]
    linarith [le_abs_self e]

theorem quantized_control_error {delta : ℝ} (hd : 0 < delta) (x v : ℝ) :
    |control (quantize delta x) (quantize delta v) - control x v| ≤ 5 * delta / 2 := by
  have hx := abs_le.mp (rounding_error hd x)
  have hv := abs_le.mp (rounding_error hd v)
  apply abs_le.mpr
  unfold SampledPD.control
  constructor <;> linarith [hx.1, hx.2, hv.1, hv.2]

theorem integrated_error {h d D : ℝ} (h0 : 0 ≤ h) (hhi : h ≤ 1 / 2)
    (hd : |d| ≤ D) : (h ^ 2 / 2 * d) ^ 2 + (h * d) ^ 2 ≤ (3 / 5 * D) ^ 2 := by
  have hd2 : d ^ 2 ≤ D ^ 2 := by nlinarith [abs_le.mp hd]
  have h2 : h ^ 2 ≤ 1 / 4 := by nlinarith
  have h4 : h ^ 4 ≤ 1 / 16 := by nlinarith [sq_nonneg (h ^ 2 - 1 / 4)]
  have hc : h ^ 4 / 4 + h ^ 2 ≤ 9 / 25 := by linarith
  have hp := mul_le_mul_of_nonneg_right hc (sq_nonneg d)
  nlinarith only [hp, hd2]

/-- Rounded feedback, hard actuator limit, and a held acceleration disturbance. -/
def input (delta U x v : ℝ) : ℝ := saturate U (control (quantize delta x) (quantize delta v))

theorem safe_step {h x v w : ℝ}
    (hlo : 1 / 20 ≤ h) (hhi : h ≤ 1 / 2)
    (hE : energy x v ≤ 1 / 10) (hw : |w| ≤ 1 / 4000) :
    energy (x + h * v + h ^ 2 / 2 * (input (1 / 10000) 1 x v + w))
      (v + h * (input (1 / 10000) 1 x v + w)) ≤ 1 / 10 := by
  have hu := control_within_limit (by norm_num : (0 : ℝ) ≤ 1) hE (by norm_num)
  let e := control (quantize (1 / 10000) x) (quantize (1 / 10000) v) - control x v
  have he : |e| ≤ 1 / 4000 := by
    have hh := quantized_control_error (by norm_num : (0 : ℝ) < 1 / 10000) x v
    norm_num at hh
    exact hh
  have hs := clipping_error (e := e) hu
  have hi : control x v + e = control (quantize (1 / 10000) x) (quantize (1 / 10000) v) := by dsimp [e]; ring
  rw [hi] at hs
  let d := input (1 / 10000) 1 x v - control x v + w
  have hd : |d| ≤ 1 / 2000 := by
    dsimp [d, input]
    exact (abs_add_le _ _).trans (by linarith)
  have herr := integrated_error (by linarith : 0 ≤ h) hhi hd
  norm_num at herr
  have herr' : (h ^ 2 / 2 * d) ^ 2 + (h * d) ^ 2 ≤ (3 / 10000 : ℝ) ^ 2 := by
    norm_num
    exact herr
  have hb := Sampling.robust_step (x := x) (v := v) hlo hhi herr'
  have hid1 : x + h * v + h ^ 2 / 2 * (input (1 / 10000) 1 x v + w) = position h x v + h ^ 2 / 2 * d := by
    dsimp [position, d]; ring
  have hid2 : v + h * (input (1 / 10000) 1 x v + w) = velocity h x v + h * d := by
    dsimp [velocity, d]; ring
  rw [hid1, hid2]
  nlinarith only [hb, hE]

theorem safe_trajectory (h x v w : ℕ → ℝ)
    (hlo : ∀ n, 1 / 20 ≤ h n) (hhi : ∀ n, h n ≤ 1 / 2)
    (hw : ∀ n, |w n| ≤ 1 / 4000) (hinit : energy (x 0) (v 0) ≤ 1 / 10)
    (hx : ∀ n, x (n + 1) = x n + h n * v n + h n ^ 2 / 2 *
      (input (1 / 10000) 1 (x n) (v n) + w n))
    (hv : ∀ n, v (n + 1) = v n + h n * (input (1 / 10000) 1 (x n) (v n) + w n)) :
    ∀ n, energy (x n) (v n) ≤ 1 / 10 := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih =>
    rw [hx n, hv n]
    exact safe_step (hlo n) (hhi n) ih (hw n)

end LeanControls.Quantized
