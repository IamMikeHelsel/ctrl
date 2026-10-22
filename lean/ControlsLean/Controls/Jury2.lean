/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# Schur stability of second-order discrete-time systems

The characteristic polynomial of `y[k+2] + a y[k+1] + b y[k] = u[k]` is `z² + a z + b`.
It is *Schur* (all complex roots in the open unit disk, i.e. the system is asymptotically
stable) iff `|b| < 1` and `|a| < 1 + b`. This is the `n = 2` case of the Jury stability
test, and the discrete-time counterpart of `isHurwitz2_iff`.
-/

namespace ControlsLean.Controls

/-- `z² + a z + b` has all its complex roots in the open unit disk. -/
def IsSchur2 (a b : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 2 + a * z + b = 0 → ‖z‖ < 1

private lemma root_parts {a b : ℝ} {z : ℂ} (h : z ^ 2 + a * z + b = 0) :
    z.re ^ 2 - z.im ^ 2 + a * z.re + b = 0 ∧ z.im * (2 * z.re + a) = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  constructor <;> linarith

private lemma norm_lt_one_of {z : ℂ} (h : z.re ^ 2 + z.im ^ 2 < 1) : ‖z‖ < 1 := by
  have h2 : ‖z‖ ^ 2 < 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 zero_le_one h2

theorem isSchur2_of_jury {a b : ℝ} (hb : |b| < 1) (ha : |a| < 1 + b) : IsSchur2 a b := by
  obtain ⟨hb1, hb2⟩ := abs_lt.1 hb
  obtain ⟨ha1, ha2⟩ := abs_lt.1 ha
  intro z hz
  obtain ⟨hre, him⟩ := root_parts hz
  apply norm_lt_one_of
  rcases mul_eq_zero.1 him with hy | hx
  · rw [hy] at hre ⊢
    have h1 : z.re < 1 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (sub_nonneg.2 hc) (by linarith : (0 : ℝ) ≤ z.re + 1 + a)]
    have h2 : -1 < z.re := by
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -1 - z.re)
        (by linarith : (0 : ℝ) ≤ 1 - a - z.re)]
    nlinarith
  · have : z.re = -a / 2 := by linarith
    rw [this] at hre ⊢
    nlinarith

/-- **Second-order Jury stability test.** -/
theorem isSchur2_iff (a b : ℝ) : IsSchur2 a b ↔ |b| < 1 ∧ |a| < 1 + b := by
  refine ⟨fun h => ?_, fun ⟨hb, ha⟩ => isSchur2_of_jury hb ha⟩
  set d := a ^ 2 - 4 * b with hd
  by_cases hd0 : 0 ≤ d
  · set s := Real.sqrt d
    have hs : s ^ 2 = d := Real.sq_sqrt hd0
    have root : ∀ r : ℝ, r ^ 2 + a * r + b = 0 → |r| < 1 := fun r hr => by
      have := h r (by exact_mod_cast hr)
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    obtain ⟨h1, h2⟩ := abs_lt.1 (root ((-a + s) / 2) (by nlinarith))
    obtain ⟨h3, h4⟩ := abs_lt.1 (root ((-a - s) / 2) (by nlinarith))
    have hb : b = (-a + s) / 2 * ((-a - s) / 2) := by nlinarith
    have hp : 0 < (1 + (-a + s) / 2) * (1 + (-a - s) / 2) := mul_pos (by linarith) (by linarith)
    have hm : 0 < (1 - (-a + s) / 2) * (1 - (-a - s) / 2) := mul_pos (by linarith) (by linarith)
    refine ⟨abs_lt.2 ⟨?_, ?_⟩, abs_lt.2 ⟨?_, ?_⟩⟩
    · rw [hb]; nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + (-a + s) / 2)
        (by linarith : (0 : ℝ) < 1 - (-a - s) / 2),
        mul_pos (by linarith : (0 : ℝ) < 1 - (-a + s) / 2)
        (by linarith : (0 : ℝ) < 1 + (-a - s) / 2)]
    · rw [hb]; nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + (-a + s) / 2)
        (by linarith : (0 : ℝ) < 1 - (-a - s) / 2),
        mul_pos (by linarith : (0 : ℝ) < 1 - (-a + s) / 2)
        (by linarith : (0 : ℝ) < 1 + (-a - s) / 2)]
    · nlinarith
    · nlinarith
  · push Not at hd0
    set s := Real.sqrt (-d)
    have hs : s ^ 2 = -d := Real.sq_sqrt (by linarith)
    have hz := h ⟨-a / 2, s / 2⟩ (by apply Complex.ext <;> simp [pow_two] <;> nlinarith)
    have hn : ‖(⟨-a / 2, s / 2⟩ : ℂ)‖ ^ 2 = b := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith
    have hb1 : b < 1 := by
      nlinarith [norm_nonneg (⟨-a / 2, s / 2⟩ : ℂ)]
    have hb0 : 0 ≤ b := by nlinarith [sq_nonneg a]
    refine ⟨abs_lt.2 ⟨by linarith, hb1⟩, abs_lt_of_sq_lt_sq ?_ (by linarith)⟩
    nlinarith [sq_nonneg (1 - b)]

/-- The Jury conditions in their textbook form: `p(1) > 0`, `p(-1) > 0`, `|p(0)| < 1`. -/
theorem isSchur2_iff_jury (a b : ℝ) :
    IsSchur2 a b ↔ 0 < 1 + a + b ∧ 0 < 1 - a + b ∧ |b| < 1 := by
  rw [isSchur2_iff, abs_lt (a := a)]
  constructor
  · rintro ⟨hb, h1, h2⟩; exact ⟨by linarith, by linarith, hb⟩
  · rintro ⟨h1, h2, hb⟩; exact ⟨hb, by linarith, by linarith⟩

/-- A Schur second-order polynomial has `|a| < 2`. -/
theorem IsSchur2.abs_lt_two {a b : ℝ} (h : IsSchur2 a b) : |a| < 2 := by
  obtain ⟨hb, ha⟩ := (isSchur2_iff a b).1 h
  linarith [(abs_lt.1 hb).2]

/-- Deadbeat control: `z²` has its only root at the origin. -/
theorem isSchur2_deadbeat : IsSchur2 0 0 :=
  isSchur2_of_jury (by simp) (by simp)

end ControlsLean.Controls
