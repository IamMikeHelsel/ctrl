import ControlsLean.Controls.Hurwitz2
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace ControlsLean.Controls

/-- `s³ + a s² + b s + c` has all complex roots in the open left half-plane. -/
def IsHurwitz3 (a b c : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 3 + a * z ^ 2 + b * z + c = 0 → z.re < 0

lemma cubic_root_parts {a b c : ℝ} {z : ℂ} (h : z ^ 3 + a * z ^ 2 + b * z + c = 0) :
    z.re ^ 3 - 3 * z.re * z.im ^ 2 + a * (z.re ^ 2 - z.im ^ 2) + b * z.re + c = 0 ∧
    z.im * (3 * z.re ^ 2 - z.im ^ 2 + 2 * a * z.re + b) = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_succ] at hre him
  constructor <;> nlinarith

/-- Sufficiency of the third-order Routh–Hurwitz conditions. -/
theorem isHurwitz3_of_routh {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : c < a * b) : IsHurwitz3 a b c := by
  intro z hz
  obtain ⟨hre, him⟩ := cubic_root_parts hz
  by_contra hx
  push Not at hx
  set x := z.re
  set y := z.im
  rcases mul_eq_zero.1 him with hy | hq
  · rw [hy] at hre
    nlinarith [pow_nonneg hx 3, sq_nonneg x, mul_nonneg ha.le (sq_nonneg x),
      mul_nonneg hb.le hx]
  · have hy2 : y ^ 2 = 3 * x ^ 2 + 2 * a * x + b := by linarith
    have key : -8 * x ^ 3 - 8 * a * x ^ 2 - (2 * b + 2 * a ^ 2) * x + (c - a * b) = 0 := by
      have : y ^ 2 = 3 * x ^ 2 + 2 * a * x + b := hy2
      nlinarith
    nlinarith [pow_nonneg hx 3, mul_nonneg ha.le (sq_nonneg x),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * b + 2 * a ^ 2) hx]

/-- Every real cubic has a real root (IVT). -/
lemma exists_real_root_cubic (a b c : ℝ) : ∃ r : ℝ, r ^ 3 + a * r ^ 2 + b * r + c = 0 := by
  set M := 1 + |a| + |b| + |c|
  have hM : 1 ≤ M := by
    have := abs_nonneg a; have := abs_nonneg b; have := abs_nonneg c; simp only [M]; linarith
  have f_cont : Continuous fun r : ℝ => r ^ 3 + a * r ^ 2 + b * r + c := by fun_prop
  have hlo : (-M) ^ 3 + a * (-M) ^ 2 + b * (-M) + c ≤ 0 := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : -b ≤ |b| := neg_le_abs b
    have h3 : c ≤ |c| := le_abs_self c
    have hM2 : M ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg M),
      mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ M),
      abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_le_mul_of_nonneg_left hM2 (abs_nonneg b),
      mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ M ^ 2) (abs_nonneg c)]
  have hhi : 0 ≤ M ^ 3 + a * M ^ 2 + b * M + c := by
    have h1 : -a ≤ |a| := neg_le_abs a
    have h2 : -b ≤ |b| := neg_le_abs b
    have h3 : -c ≤ |c| := neg_le_abs c
    have hM2 : M ≤ M ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg M),
      mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ M),
      abs_nonneg a, abs_nonneg b, abs_nonneg c, mul_le_mul_of_nonneg_left hM2 (abs_nonneg b),
      mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ M ^ 2) (abs_nonneg c)]
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc (by linarith : -M ≤ M) f_cont.continuousOn
    ⟨hlo, hhi⟩
  exact ⟨r, hr⟩

/-- Necessity of the third-order Routh–Hurwitz conditions, via real-root factorization
`s³ + a s² + b s + c = (s - r)(s² + p s + q)`. -/
theorem routh_of_isHurwitz3 {a b c : ℝ} (h : IsHurwitz3 a b c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ c < a * b := by
  obtain ⟨r, hr⟩ := exists_real_root_cubic a b c
  have hr0 : r < 0 := by
    have := h r (by exact_mod_cast hr)
    simpa using this
  set p := a + r
  set q := b + r * p
  have hc : c = -r * q := by simp only [p, q]; nlinarith
  have h2 : IsHurwitz2 p q := by
    intro z hz
    apply h z
    have hp' : (p : ℂ) = a + r := by simp [p]
    have hq' : (q : ℂ) = b + r * p := by simp [q]
    have hc' : (c : ℂ) = -r * q := by exact_mod_cast hc
    have hfac : z ^ 3 + a * z ^ 2 + b * z + c = (z - r) * (z ^ 2 + p * z + q) := by
      linear_combination (-z ^ 2) * hp' + (-z) * hq' + hc'
    rw [hfac, hz, mul_zero]
  obtain ⟨hp, hq⟩ := (isHurwitz2_iff p q).1 h2
  have ha : a = p - r := by simp [p]
  have hb : b = q - r * p := by simp [q]
  refine ⟨by linarith, by nlinarith, by rw [hc]; nlinarith, ?_⟩
  rw [ha, hb, hc]
  nlinarith [mul_pos (mul_pos hp hp) (neg_pos.2 hr0), mul_pos hp (mul_pos (neg_pos.2 hr0) (neg_pos.2 hr0))]

/-- **Third-order Routh–Hurwitz criterion.** -/
theorem isHurwitz3_iff (a b c : ℝ) :
    IsHurwitz3 a b c ↔ 0 < a ∧ 0 < b ∧ 0 < c ∧ c < a * b :=
  ⟨routh_of_isHurwitz3, fun ⟨ha, hb, hc, h⟩ => isHurwitz3_of_routh ha hb hc h⟩

/-- PID on a double integrator: `ÿ = u`, `u = -kp y - kd ẏ - ki ∫y` gives
`s³ + kd s² + kp s + ki`; stable iff `kd, kp, ki > 0` and `ki < kd kp`. -/
theorem pid_doubleIntegrator_hurwitz_iff (kp ki kd : ℝ) :
    IsHurwitz3 kd kp ki ↔ 0 < kd ∧ 0 < kp ∧ 0 < ki ∧ ki < kd * kp :=
  isHurwitz3_iff kd kp ki

/-- Boundary case: `ab = c` gives a pure imaginary pair `±i√b`, so not Hurwitz. -/
example : ¬ IsHurwitz3 1 1 1 := by
  intro h
  have := h Complex.I (by ring_nf; simp [Complex.I_sq])
  simp at this

end ControlsLean.Controls
