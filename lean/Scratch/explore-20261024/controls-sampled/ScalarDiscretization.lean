import Mathlib

/-!
Scalar discretizations of `ẋ = a x` (or `ẋ = z x` for complex `z`):
exact (ZOH), forward Euler, backward Euler, Tustin; plus the delay equation
`ẋ = -k x(t-τ)` crossing at `kτ = π/2`.
-/

open Complex

namespace SampledExplore

/-- Exact sampling: `a < 0`, `T > 0` gives `|exp(aT)| < 1`. -/
theorem abs_exp_lt_one {a T : ℝ} (ha : a < 0) (hT : 0 < T) : |Real.exp (a * T)| < 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos ha hT

/-- Complex exact sampling: `‖exp(zT)‖ < 1 ↔ Re z < 0` for `T > 0`. -/
theorem norm_exp_lt_one_iff {z : ℂ} {T : ℝ} (hT : 0 < T) :
    ‖Complex.exp (z * T)‖ < 1 ↔ z.re < 0 := by
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  constructor
  · intro h; by_contra h'; push Not at h'; nlinarith
  · intro h; nlinarith

/-- Forward Euler `x⁺ = (1 + h a) x`, `a < 0`, `h > 0`: stable iff `h < 2 / |a|`. -/
theorem forwardEuler_stable_iff {a h : ℝ} (ha : a < 0) (hh : 0 < h) :
    |1 + h * a| < 1 ↔ h < 2 / |a| := by
  rw [abs_of_neg ha, lt_div_iff₀ (by linarith), abs_lt]
  constructor
  · rintro ⟨h1, _⟩; nlinarith
  · intro h1; constructor <;> nlinarith

/-- Forward Euler for complex `z`: `‖1 + h z‖ < 1 ↔ h ‖z‖² < -2 Re z`. -/
theorem forwardEuler_complex_stable_iff {z : ℂ} {h : ℝ} (hh : 0 < h) :
    ‖1 + (h : ℂ) * z‖ < 1 ↔ h * (z.re ^ 2 + z.im ^ 2) < -2 * z.re := by
  have key : ‖1 + (h : ℂ) * z‖ ^ 2 = 1 + h * (2 * z.re + h * (z.re ^ 2 + z.im ^ 2)) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  rw [← sq_lt_one_iff₀ (norm_nonneg _), key]
  constructor
  · intro H
    have : h * (2 * z.re + h * (z.re ^ 2 + z.im ^ 2)) < 0 := by linarith
    have h2 : 2 * z.re + h * (z.re ^ 2 + z.im ^ 2) < 0 := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  · intro H
    have : 2 * z.re + h * (z.re ^ 2 + z.im ^ 2) < 0 := by nlinarith
    nlinarith

/-- Forward Euler destroys marginal (undamped) oscillators for every step size. -/
theorem forwardEuler_unstable_of_re_eq_zero {z : ℂ} (hz : z.re = 0) (hz0 : z ≠ 0) {h : ℝ}
    (hh : 0 < h) : 1 < ‖1 + (h : ℂ) * z‖ := by
  have him : z.im ≠ 0 := by
    intro him; exact hz0 (Complex.ext hz him)
  have key : ‖1 + (h : ℂ) * z‖ ^ 2 = 1 + h ^ 2 * z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hz]; ring
  have : 1 < ‖1 + (h : ℂ) * z‖ ^ 2 := by
    rw [key]; have := pow_pos hh 2; have := pow_pos (abs_pos.mpr him) 2
    rw [sq_abs] at this; nlinarith
  nlinarith [norm_nonneg (1 + (h : ℂ) * z)]

/-- Backward Euler `x⁺ = x / (1 - h a)` is stable for every `h > 0` when `a < 0`. -/
theorem backwardEuler_stable {a h : ℝ} (ha : a < 0) (hh : 0 < h) : |1 / (1 - h * a)| < 1 := by
  have hpos : 1 < 1 - h * a := by nlinarith
  rw [abs_of_pos (by positivity), div_lt_one (by linarith)]
  exact hpos

/-- Backward Euler, complex: `Re z < 0` implies `‖1 / (1 - h z)‖ < 1` for every `h > 0`. -/
theorem backwardEuler_complex_stable {z : ℂ} (hz : z.re < 0) {h : ℝ} (hh : 0 < h) :
    ‖1 / (1 - (h : ℂ) * z)‖ < 1 := by
  have hre : (1 - (h : ℂ) * z).re = 1 - h * z.re := by simp
  have h1 : (1 : ℝ) < (1 - (h : ℂ) * z).re := by rw [hre]; nlinarith
  have hgt : 1 < ‖1 - (h : ℂ) * z‖ := lt_of_lt_of_le h1 (Complex.re_le_norm _)
  rw [norm_div, norm_one, div_lt_one (by linarith)]
  exact hgt

/-- Key identity for Tustin: `‖1+w‖² - ‖1-w‖² = 4 Re w`. -/
theorem normSq_one_add_sub_one_sub (w : ℂ) :
    ‖1 + w‖ ^ 2 - ‖1 - w‖ ^ 2 = 4 * w.re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp; ring

/-- Tustin / bilinear map: for `h > 0` and `z ≠ 2/h`,
`‖(1 + z h/2) / (1 - z h/2)‖ < 1 ↔ Re z < 0`. -/
theorem tustin_norm_lt_one_iff {z : ℂ} {h : ℝ} (hh : 0 < h)
    (hden : 1 - z * h / 2 ≠ 0) :
    ‖(1 + z * h / 2) / (1 - z * h / 2)‖ < 1 ↔ z.re < 0 := by
  have hpos : 0 < ‖1 - z * h / 2‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_lt_one hpos, ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← sub_neg, normSq_one_add_sub_one_sub]
  have : (z * (h : ℂ) / 2).re = z.re * h / 2 := by simp
  rw [this]
  constructor
  · intro H; by_contra H'; push Not at H'; nlinarith
  · intro H; nlinarith

/-- Tustin maps the imaginary axis onto the unit circle. -/
theorem tustin_norm_eq_one_of_re_eq_zero {z : ℂ} {h : ℝ} (hz : z.re = 0)
    (hden : 1 - z * h / 2 ≠ 0) :
    ‖(1 + z * h / 2) / (1 - z * h / 2)‖ = 1 := by
  have hpos : 0 < ‖1 - z * h / 2‖ := norm_pos_iff.mpr hden
  rw [norm_div, div_eq_one_iff_eq hpos.ne']
  have h4 := normSq_one_add_sub_one_sub (z * h / 2)
  have : (z * (h : ℂ) / 2).re = 0 := by simp [hz]
  rw [this, mul_zero, sub_eq_zero] at h4
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h4

/-- In the left half-plane the Tustin denominator never vanishes. -/
theorem tustin_den_ne_zero {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : z.re < 0) :
    1 - z * h / 2 ≠ 0 := by
  intro H
  have := congrArg Complex.re H
  simp at this
  nlinarith

/-- Delay equation `ẋ = -k x(t-τ)`: characteristic function `s + k e^{-sτ}`.
At `kτ = π/2` the pure imaginary point `s = i k` is a root. -/
theorem delay_char_root_at_crossing {k τ : ℝ} (hkτ : k * τ = Real.pi / 2) :
    (I * k) + k * Complex.exp (-(I * k) * τ) = 0 := by
  have : -(I * (k : ℂ)) * τ = -(((Real.pi / 2 : ℝ) : ℂ) * I) := by
    rw [← hkτ]; push_cast; ring
  have he : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  rw [this, Complex.exp_neg, he, Complex.inv_I]; ring

/-- Below the crossing `kτ < π/2` (with `k > 0`, `τ ≥ 0`), `s + k e^{-sτ}` has no root on the
imaginary axis. -/
theorem delay_char_no_imag_root {k τ : ℝ} (hk : 0 < k) (hτ : 0 ≤ τ)
    (hkτ : k * τ < Real.pi / 2) (ω : ℝ) :
    (I * ω) + k * Complex.exp (-(I * ω) * τ) ≠ 0 := by
  intro H
  have harg : -(I * (ω : ℂ)) * τ = ((-(ω * τ) : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at H
  have hre := congrArg Complex.re H
  have him := congrArg Complex.im H
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
    Real.cos_neg, Real.sin_neg] at hre him
  have hcos : Real.cos (ω * τ) = 0 := by
    have : k * Real.cos (ω * τ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk.ne'
    · exact h
  have hω : |ω| ≤ k := by
    have : ω = k * Real.sin (ω * τ) := by linarith
    rw [this, abs_mul, abs_of_pos hk]
    exact mul_le_of_le_one_right hk.le (Real.abs_sin_le_one _)
  have hb : |ω * τ| < Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg hτ]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hω hτ) hkτ
  rw [abs_lt] at hb
  have := Real.cos_pos_of_mem_Ioo ⟨hb.1, hb.2⟩
  linarith

end SampledExplore

#print axioms SampledExplore.forwardEuler_stable_iff
#print axioms SampledExplore.forwardEuler_complex_stable_iff
#print axioms SampledExplore.forwardEuler_unstable_of_re_eq_zero
#print axioms SampledExplore.backwardEuler_complex_stable
#print axioms SampledExplore.tustin_norm_lt_one_iff
#print axioms SampledExplore.tustin_norm_eq_one_of_re_eq_zero
#print axioms SampledExplore.delay_char_root_at_crossing
#print axioms SampledExplore.delay_char_no_imag_root
#print axioms SampledExplore.norm_exp_lt_one_iff
