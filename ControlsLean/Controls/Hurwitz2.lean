/-
Copyright (c) 2026 ControlsLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ControlsLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# Hurwitz stability of second-order systems

The characteristic polynomial of `ÿ + a ẏ + b y = u` is `s² + a s + b`.
It is *Hurwitz* (all complex roots in the open left half-plane, i.e. the system is
asymptotically stable) iff `a > 0` and `b > 0`. This is the `n = 2` case of the
Routh–Hurwitz criterion.
-/

namespace ControlsLean.Controls

/-- `s² + a s + b` has all its complex roots in the open left half-plane. -/
def IsHurwitz2 (a b : ℝ) : Prop :=
  ∀ z : ℂ, z ^ 2 + a * z + b = 0 → z.re < 0

private lemma root_parts {a b : ℝ} {z : ℂ} (h : z ^ 2 + a * z + b = 0) :
    z.re ^ 2 - z.im ^ 2 + a * z.re + b = 0 ∧ z.im * (2 * z.re + a) = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  constructor <;> linarith

theorem isHurwitz2_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IsHurwitz2 a b := by
  intro z hz
  obtain ⟨hre, him⟩ := root_parts hz
  rcases mul_eq_zero.1 him with hy | hx
  · by_contra hpos
    push Not at hpos
    rw [hy] at hre
    nlinarith
  · linarith

/-- An explicit root with nonnegative real part when the coefficients are not both positive. -/
private lemma exists_root_re_nonneg {a b : ℝ} (h : a ≤ 0 ∨ b ≤ 0) :
    ∃ z : ℂ, z ^ 2 + a * z + b = 0 ∧ 0 ≤ z.re := by
  set d := a ^ 2 - 4 * b with hd
  by_cases hd0 : 0 ≤ d
  · set s := Real.sqrt d
    have hs : s ^ 2 = d := Real.sq_sqrt hd0
    have hs0 : 0 ≤ s := Real.sqrt_nonneg d
    refine ⟨((-a + s) / 2 : ℝ), ?_, ?_⟩
    · have : ((-a + s) / 2) ^ 2 + a * ((-a + s) / 2) + b = 0 := by nlinarith
      exact_mod_cast this
    · simp only [Complex.ofReal_re]
      rcases h with ha | hb
      · linarith
      · nlinarith [sq_nonneg (s - a), sq_nonneg (s + a)]
  · push Not at hd0
    set s := Real.sqrt (-d)
    have hs : s ^ 2 = -d := Real.sq_sqrt (by linarith)
    have ha : a ≤ 0 := h.resolve_right (by nlinarith [sq_nonneg a])
    refine ⟨⟨-a / 2, s / 2⟩, ?_, by simp; linarith⟩
    apply Complex.ext <;> simp [pow_two] <;> nlinarith

/-- **Second-order Routh–Hurwitz criterion.** -/
theorem isHurwitz2_iff (a b : ℝ) : IsHurwitz2 a b ↔ 0 < a ∧ 0 < b := by
  refine ⟨fun h => ?_, fun ⟨ha, hb⟩ => isHurwitz2_of_pos ha hb⟩
  by_contra hn
  rw [not_and_or, not_lt, not_lt] at hn
  obtain ⟨z, hz, hre⟩ := exists_root_re_nonneg hn
  exact absurd (h z hz) (not_lt.2 hre)

/-- Mass–spring–damper `m ÿ + c ẏ + k y = 0` with positive parameters is asymptotically
stable. -/
theorem massSpringDamper_hurwitz {m c k : ℝ} (hm : 0 < m) (hc : 0 < c) (hk : 0 < k) :
    IsHurwitz2 (c / m) (k / m) :=
  isHurwitz2_of_pos (div_pos hc hm) (div_pos hk hm)

/-- PD control of a double integrator `ÿ = u`, `u = -k_p y - k_d ẏ`, is stable
iff both gains are positive. -/
theorem pd_doubleIntegrator_hurwitz_iff (kp kd : ℝ) :
    IsHurwitz2 kd kp ↔ 0 < kd ∧ 0 < kp :=
  isHurwitz2_iff kd kp

end ControlsLean.Controls
