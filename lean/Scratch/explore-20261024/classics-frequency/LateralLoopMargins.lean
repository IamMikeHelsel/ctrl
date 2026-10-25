import Mathlib

/-!
# Gain and phase margins of `L(s) = K / (s (τ s + 1))` (Nyquist 1932, Bode 1945)

An integrator plus first-order lag: the classical model of a lateral (steering) loop such as
openpilot's, with `K` the loop gain and `τ` the actuator / steering-rack lag.

* `loopTF_re`, `loopTF_im`: the Nyquist plot `L(iω)` in closed form.
* `loopTF_im_neg`: for `ω > 0` the plot stays strictly below the real axis, so there is no phase
  crossover: **infinite gain margin** (`one_add_gain_mul_loopTF_ne_zero`).
* `closedLoop_roots_stable`: for every gain `k > 0`, the closed-loop poles
  `τ s² + s + k K = 0` lie in the open left half-plane (2nd-order Routh–Hurwitz).
* `norm_loopTF_eq_one_iff`: gain crossover `|L(iω_c)| = 1 ↔ ω_c² (1 + τ² ω_c²) = K²`.
* `phaseMargin_eq`: phase margin `arg(-L(iω_c)) = arctan(1 / (τ ω_c))`, in `(0, π/2)`.
* `golden_crossover`: for `K = τ = 1`, `ω_c² = (√5 - 1)/2 = 1/φ`.
-/

open Complex Real

namespace ClassicsFrequency

/-- Loop transfer function `L(s) = K / (s (τ s + 1))`. -/
noncomputable def loopTF (K τ : ℝ) (s : ℂ) : ℂ := K / (s * (τ * s + 1))

theorem loopTF_I_eq (K τ ω : ℝ) (hω : ω ≠ 0) :
    loopTF K τ (ω * I) =
      ⟨-(K * τ) / (1 + τ ^ 2 * ω ^ 2), -K / (ω * (1 + τ ^ 2 * ω ^ 2))⟩ := by
  have hd : (1 + τ ^ 2 * ω ^ 2) ≠ 0 := by positivity
  have hden : (ω : ℂ) * I * (τ * (ω * I) + 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hω) I_ne_zero) ?_
    intro h
    have := congrArg Complex.re h
    simp at this
  unfold loopTF
  rw [div_eq_iff hden]
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem loopTF_re (K τ ω : ℝ) (hω : ω ≠ 0) :
    (loopTF K τ (ω * I)).re = -(K * τ) / (1 + τ ^ 2 * ω ^ 2) := by
  rw [loopTF_I_eq K τ ω hω]

theorem loopTF_im (K τ ω : ℝ) (hω : ω ≠ 0) :
    (loopTF K τ (ω * I)).im = -K / (ω * (1 + τ ^ 2 * ω ^ 2)) := by
  rw [loopTF_I_eq K τ ω hω]

/-- No phase crossover: the Nyquist plot never touches the real axis for `ω > 0`. -/
theorem loopTF_im_neg {K τ ω : ℝ} (hK : 0 < K) (hω : 0 < ω) :
    (loopTF K τ (ω * I)).im < 0 := by
  rw [loopTF_im K τ ω hω.ne']
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- **Infinite gain margin**: no positive gain `k` brings `1 + k L(iω)` to zero. -/
theorem one_add_gain_mul_loopTF_ne_zero {K τ ω k : ℝ} (hK : 0 < K) (hω : 0 < ω) (hk : 0 < k) :
    1 + k * loopTF K τ (ω * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  rcases this with h1 | h1
  · exact hk.ne' h1
  · exact (loopTF_im_neg (τ := τ) hK hω).ne h1

/-- **Closed loop is stable for every gain** (`τ, k K > 0`): roots of `τ s² + s + c` have
negative real part. -/
theorem closedLoop_roots_stable {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c) {s : ℂ}
    (hs : τ * s ^ 2 + s + c = 0) : s.re < 0 := by
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp [pow_two] at hre him
  rcases eq_or_ne s.im 0 with hy | hy
  · rw [hy] at hre
    nlinarith [sq_nonneg s.re]
  · have : s.re = -1 / (2 * τ) := by
      field_simp
      have : s.im * (2 * τ * s.re + 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hy
      · linarith
    rw [this]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem normSq_loopTF {K τ ω : ℝ} (hω : ω ≠ 0) :
    normSq (loopTF K τ (ω * I)) = K ^ 2 / (ω ^ 2 * (1 + τ ^ 2 * ω ^ 2)) := by
  have hd : (1 + τ ^ 2 * ω ^ 2) ≠ 0 := by positivity
  rw [normSq_apply, loopTF_re K τ ω hω, loopTF_im K τ ω hω]
  field_simp
  ring

/-- **Gain crossover condition.** -/
theorem norm_loopTF_eq_one_iff {K τ ω : ℝ} (hω : ω ≠ 0) :
    ‖loopTF K τ (ω * I)‖ = 1 ↔ ω ^ 2 * (1 + τ ^ 2 * ω ^ 2) = K ^ 2 := by
  have hd : 0 < ω ^ 2 * (1 + τ ^ 2 * ω ^ 2) := by positivity
  have key : ‖loopTF K τ (ω * I)‖ ^ 2 = K ^ 2 / (ω ^ 2 * (1 + τ ^ 2 * ω ^ 2)) := by
    rw [← normSq_eq_norm_sq, normSq_loopTF hω]
  constructor
  · intro h
    rw [h, one_pow, eq_div_iff hd.ne', one_mul] at key
    exact key
  · intro h
    rw [← h, div_self hd.ne'] at key
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 key

/-- Phase margin `PM = π + ∠L(iω)`, i.e. the angle of `-L(iω)`. -/
noncomputable def phaseMarginAt (K τ ω : ℝ) : ℝ := arg (-loopTF K τ (ω * I))

/-- **Phase margin formula**: `PM(ω) = arctan(1 / (τ ω))` for all `ω > 0` (in particular at the
gain crossover). -/
theorem phaseMargin_eq {K τ ω : ℝ} (hK : 0 < K) (hτ : 0 < τ) (hω : 0 < ω) :
    phaseMarginAt K τ ω = Real.arctan (1 / (τ * ω)) := by
  set z := -loopTF K τ (ω * I)
  have hre : 0 < z.re := by
    simp only [z, neg_re, loopTF_re K τ ω hω.ne']
    rw [neg_div, neg_neg]; positivity
  have hratio : z.im / z.re = 1 / (τ * ω) := by
    simp only [z, neg_re, neg_im, loopTF_re K τ ω hω.ne', loopTF_im K τ ω hω.ne']
    have hd : (1 + τ ^ 2 * ω ^ 2) ≠ 0 := by positivity
    field_simp
  have habs : |arg z| < π / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  rw [phaseMarginAt, ← hratio, ← tan_arg, arctan_tan (abs_lt.1 habs).1 (abs_lt.1 habs).2]

theorem phaseMargin_pos {K τ ω : ℝ} (hK : 0 < K) (hτ : 0 < τ) (hω : 0 < ω) :
    0 < phaseMarginAt K τ ω ∧ phaseMarginAt K τ ω < π / 2 := by
  rw [phaseMargin_eq hK hτ hω]
  exact ⟨arctan_pos.2 (by positivity), arctan_lt_pi_div_two _⟩

/-- Crossover frequency in closed form: `ω_c² = (√(1 + 4 τ² K²) - 1) / (2 τ²)`. -/
theorem crossover_closed_form {K τ : ℝ} (hτ : 0 < τ) :
    let w2 := (√(1 + 4 * τ ^ 2 * K ^ 2) - 1) / (2 * τ ^ 2)
    w2 * (1 + τ ^ 2 * w2) = K ^ 2 := by
  intro w2
  have hs : √(1 + 4 * τ ^ 2 * K ^ 2) ^ 2 = 1 + 4 * τ ^ 2 * K ^ 2 := sq_sqrt (by positivity)
  have : τ ^ 2 ≠ 0 := by positivity
  simp only [w2]
  field_simp
  nlinarith [hs]

/-- Golden-ratio crossover for `K = τ = 1`: `|L(iω_c)| = 1` with `ω_c² = (√5 - 1)/2`. -/
theorem golden_crossover :
    ‖loopTF 1 1 (√((√5 - 1) / 2) * I)‖ = 1 := by
  have h5 : 1 < √5 := by
    rw [show (1 : ℝ) = √1 by simp]; exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : 0 < (√5 - 1) / 2 := by linarith
  have hω : √((√5 - 1) / 2) ≠ 0 := (sqrt_pos.2 hpos).ne'
  rw [norm_loopTF_eq_one_iff hω, sq_sqrt hpos.le]
  have : √5 ^ 2 = 5 := sq_sqrt (by norm_num)
  nlinarith

end ClassicsFrequency
