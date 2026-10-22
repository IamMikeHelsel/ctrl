/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Controls.Hurwitz2
import Mathlib.Topology.Order.IntermediateValue

/-!
# Hurwitz stability of third-order systems

The characteristic polynomial of `y⃛ + a ÿ + b ẏ + c y = u` is `s³ + a s² + b s + c`.
It is *Hurwitz* (all complex roots in the open left half-plane) iff
`a > 0`, `b > 0`, `c > 0` and `a b > c`. This is the `n = 3` case of the Routh–Hurwitz
criterion.

## Main results

* `isHurwitz3_of_pos`: sufficiency, by eliminating the imaginary part of a root.
* `isHurwitz3_iff`: the full criterion. Necessity factors the cubic as
  `(s + r)(s² + p s + q)` over `ℝ` (a real cubic has a real root, by the intermediate value
  theorem) and reuses `isHurwitz2_iff`; then `a b - c = p (r² + p r + q)`.
* `cubic_123_hurwitz`: `s³ + 6 s² + 11 s + 6 = (s + 1)(s + 2)(s + 3)` is Hurwitz.
* `pGain_s_s1_s2_hurwitz_iff`: proportional feedback `u = K (r - y)` around the plant
  `1 / (s (s + 1) (s + 2))` is stable iff `0 < K < 6`.
-/

namespace ControlsLean.Controls

/-- `s³ + a s² + b s + c` has all its complex roots in the open left half-plane. -/
def IsHurwitz3 (a b c : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 3 + a * z ^ 2 + b * z + c = 0 → z.re < 0

private lemma root_parts3 {a b c : ℝ} {z : ℂ} (h : z ^ 3 + a * z ^ 2 + b * z + c = 0) :
    z.re ^ 3 - 3 * z.re * z.im ^ 2 + a * (z.re ^ 2 - z.im ^ 2) + b * z.re + c = 0 ∧
      z.im * (3 * z.re ^ 2 - z.im ^ 2 + 2 * a * z.re + b) = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_succ] at hre him
  constructor <;> nlinarith

/-- **Third-order Routh–Hurwitz, sufficiency.** -/
theorem isHurwitz3_of_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : c < a * b) : IsHurwitz3 a b c := by
  intro z hz
  obtain ⟨hre, him⟩ := root_parts3 hz
  by_contra hpos
  push Not at hpos
  rcases mul_eq_zero.1 him with hy | hy
  · rw [hy] at hre
    nlinarith [pow_nonneg hpos 3, sq_nonneg z.re]
  · have hy2 : z.im ^ 2 = 3 * z.re ^ 2 + 2 * a * z.re + b := by linarith
    rw [hy2] at hre
    nlinarith [pow_nonneg hpos 3, sq_nonneg z.re, mul_nonneg ha.le hpos,
      mul_nonneg (mul_nonneg ha.le hpos) hpos]

/-- A real cubic has a real root. -/
private lemma exists_real_root (a b c : ℝ) : ∃ x : ℝ, x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
  set f : ℝ → ℝ := fun x => x ^ 3 + a * x ^ 2 + b * x + c with hf
  set M := 1 + |a| + |b| + |c| with hM
  have hM1 : 1 ≤ M := by linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
  have hM0 : 0 ≤ M := by linarith
  have hMa : 1 + |b| + |c| ≤ M + a := by linarith [neg_abs_le a]
  have hMa' : 1 + |b| + |c| ≤ M - a := by linarith [le_abs_self a]
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hfM : 0 ≤ f M := by
    have h1 : M ^ 2 * (1 + |b| + |c|) ≤ M ^ 2 * (M + a) :=
      mul_le_mul_of_nonneg_left hMa (sq_nonneg M)
    have h2 : |b| * M ≤ |b| * M ^ 2 := mul_le_mul_of_nonneg_left hMM (abs_nonneg b)
    have h3 : |c| ≤ |c| * M ^ 2 := by nlinarith [abs_nonneg c]
    have h4 : -(|b| * M) ≤ b * M := by nlinarith [neg_abs_le b]
    simp only [hf]
    nlinarith [neg_abs_le c]
  have hfM' : f (-M) ≤ 0 := by
    have h1 : M ^ 2 * (1 + |b| + |c|) ≤ M ^ 2 * (M - a) :=
      mul_le_mul_of_nonneg_left hMa' (sq_nonneg M)
    have h2 : |b| * M ≤ |b| * M ^ 2 := mul_le_mul_of_nonneg_left hMM (abs_nonneg b)
    have h3 : |c| ≤ |c| * M ^ 2 := by nlinarith [abs_nonneg c]
    have h4 : -(b * M) ≤ |b| * M := by nlinarith [neg_abs_le b]
    simp only [hf]
    have : (-M) ^ 3 + a * (-M) ^ 2 + b * -M + c = -(M ^ 2 * (M - a)) - b * M + c := by ring
    rw [this]
    nlinarith [le_abs_self c]
  have hcont : ContinuousOn f (Set.Icc (-M) M) := by
    simp only [hf]; fun_prop
  obtain ⟨x, -, hx⟩ :=
    intermediate_value_Icc (by linarith) hcont ⟨hfM', hfM⟩
  exact ⟨x, hx⟩

/-- **Third-order Routh–Hurwitz criterion.** -/
theorem isHurwitz3_iff (a b c : ℝ) :
    IsHurwitz3 a b c ↔ 0 < a ∧ 0 < b ∧ 0 < c ∧ c < a * b := by
  refine ⟨fun h => ?_, fun ⟨ha, hb, hc, habc⟩ => isHurwitz3_of_pos ha hb hc habc⟩
  obtain ⟨x, hx⟩ := exists_real_root a b c
  set r := -x with hr
  set p := a - r with hp
  set q := b - r * p with hq
  have hc : c = r * q := by
    simp only [hq, hp, hr]; linarith
  have hfac : ∀ z : ℂ, z ^ 3 + a * z ^ 2 + b * z + c =
      (z + r) * (z ^ 2 + p * z + q) := by
    intro z
    have ha' : (a : ℂ) = r + p := by simp only [hp]; push_cast; ring
    have hb' : (b : ℂ) = q + r * p := by simp only [hq]; push_cast; ring
    have hc' : (c : ℂ) = r * q := by rw [hc]; push_cast; ring
    rw [ha', hb', hc']; ring
  have hr0 : 0 < r := by
    have := h (-r) (by rw [hfac]; ring)
    simpa using this
  have h2 : IsHurwitz2 p q := fun z hz => h z (by rw [hfac, hz, mul_zero])
  obtain ⟨hp0, hq0⟩ := (isHurwitz2_iff p q).1 h2
  have ha : a = r + p := by simp only [hp]; ring
  have hb : b = q + r * p := by simp only [hq]; ring
  refine ⟨by linarith, by rw [hb]; positivity, by rw [hc]; positivity, ?_⟩
  have : a * b - c = p * (r ^ 2 + p * r + q) := by rw [ha, hb, hc]; ring
  nlinarith [mul_pos hp0 (by positivity : 0 < r ^ 2 + p * r + q)]

/-- `s³ + 6 s² + 11 s + 6 = (s + 1)(s + 2)(s + 3)` is Hurwitz. -/
theorem cubic_123_hurwitz : IsHurwitz3 6 11 6 :=
  isHurwitz3_of_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Proportional feedback `u = K (r - y)` around the plant `1 / (s (s + 1) (s + 2))` gives
the closed-loop characteristic polynomial `s³ + 3 s² + 2 s + K`, which is Hurwitz iff
`0 < K < 6` (the textbook ultimate gain is `K = 6`). -/
theorem pGain_s_s1_s2_hurwitz_iff (K : ℝ) : IsHurwitz3 3 2 K ↔ 0 < K ∧ K < 6 := by
  rw [isHurwitz3_iff]
  constructor
  · rintro ⟨-, -, hK, hK6⟩; exact ⟨hK, by linarith⟩
  · rintro ⟨hK, hK6⟩; exact ⟨by norm_num, by norm_num, hK, by linarith⟩

end ControlsLean.Controls
