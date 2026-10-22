import Mathlib.Tactic

/-! AI-assisted, 2026-10-21. Known one-dimensional stopping-distance algebra.
These theorems bound explicit polynomial segments, not a physical robot or the
Python implementation. Dynamics-to-polynomial comparison, valid state/latency/
braking bounds, and holding rest are separate obligations. No novelty claim.
No approved Challenge depends on this exploratory module. -/

namespace Research.LatencyBraking

/-- Completing the square bounds every point of the constant-braking segment. -/
theorem brake_segment_bound (w b s : ℝ) (hb : 0 < b) :
    w * s - b * s ^ 2 / 2 ≤ w ^ 2 / (2 * b) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)).2
  nlinarith [sq_nonneg (w - b * s)]

/-- The reaction segment increases up to the maximum delay under u,A ≥ 0. -/
theorem reaction_segment_bound (u A t τ : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ A) (ht : 0 ≤ t) (hτ : t ≤ τ) :
    u * t + A * t ^ 2 / 2 ≤ u * τ + A * τ ^ 2 / 2 := by
  have hsq : t ^ 2 ≤ τ ^ 2 := by nlinarith
  have hm := mul_nonneg hA (sub_nonneg.mpr hsq)
  have hv := mul_nonneg hu (sub_nonneg.mpr hτ)
  nlinarith

/-- Both polynomial phases stay below the derived stopping envelope. The
right-hand side is derived here, never assumed as a safety hypothesis. -/
theorem delayed_braking_envelope (p u A τ b : ℝ)
    (hu : 0 ≤ u) (hA : 0 ≤ A) (_hτ : 0 ≤ τ) (hb : 0 < b) :
    (∀ t : ℝ, 0 ≤ t → t ≤ τ →
      p + u * t + A * t ^ 2 / 2 ≤
        p + u * τ + A * τ ^ 2 / 2 + (u + A * τ) ^ 2 / (2 * b)) ∧
    (∀ s : ℝ,
      p + u * τ + A * τ ^ 2 / 2 + (u + A * τ) * s - b * s ^ 2 / 2 ≤
        p + u * τ + A * τ ^ 2 / 2 + (u + A * τ) ^ 2 / (2 * b)) := by
  constructor
  · intro t ht htτ
    have hr := reaction_segment_bound u A t τ hu hA ht htτ
    have hstop : 0 ≤ (u + A * τ) ^ 2 / (2 * b) := by positivity
    linarith
  · intro s
    have h := brake_segment_bound (u + A * τ) b s hb
    linarith

/-- Exact witness: a nominal 1/4 m stop can require 273/400 m with the stated
uncertainty and delay. This is an arithmetic example, not a headline theorem. -/
theorem nominal_rule_counterexample :
    (1 : ℝ) ^ 2 / (2 * 2) < 1 / 2 ∧
    (1 : ℝ) / 2 < 1 / 50 + (11 / 10) * (1 / 5) + (1 / 5) ^ 2 / 2 +
      ((11 / 10) + (1 / 5)) ^ 2 / (2 * 2) := by
  norm_num

#print axioms brake_segment_bound
#print axioms reaction_segment_bound
#print axioms delayed_braking_envelope
#print axioms nominal_rule_counterexample

end Research.LatencyBraking
