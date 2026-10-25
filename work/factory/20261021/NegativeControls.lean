import Mathlib

/-! Codex-authored negative controls for the five frozen factory contracts.
These exact witnesses test tempting weakened conclusions; they are not proofs
of the full research questions, and were not authored by the local model. -/
namespace FactoryNegativeControls

/-- Clock curvature contributes acceleration even when nominal acceleration is zero.
The actual differentiable composition is the separate R03 factory obligation. -/
theorem clock_curvature_term_cannot_be_dropped :
    (0 : ℝ) * 0 ^ 2 + 1 * 1 > 0 * 0 ^ 2 := by norm_num

/-- Equal capacity can cover; the contradiction requires strict shortfall. -/
theorem equal_capacity_can_cover :
    (∀ x ∈ ({0} : Finset ℕ), x ∈ ({0} : Finset ℕ)) ∧
    ({0} : Finset ℕ).card = 1 := by simp

/-- A steady envelope alone cannot replace the initial transient. -/
theorem initial_transient_cannot_be_dropped :
    (1 : ℝ) > 0 ∧ (1 : ℝ) ≤ (1 / 2) ^ (0 : ℕ) * (1 - 0) + 0 := by norm_num

/-- Endpoint nonnegativity alone misses a strict within-hold violation. -/
theorem endpoints_do_not_bound_remainder :
    (0 : ℝ) ≤ 1 - 8 * 0 * (1 - 0) ∧
    (0 : ℝ) ≤ 1 - 8 * 1 * (1 - 1) ∧
    (1 : ℝ) - 8 * (1 / 2) * (1 - 1 / 2) < 0 := by norm_num

/-- A non-strict depth margin permits the projective denominator to vanish. -/
theorem nonstrict_depth_margin_can_vanish :
    (0 : ℝ) < 1 ∧ |(-1 : ℝ)| ≤ 1 ∧ ¬ (0 : ℝ) < 1 + (-1) := by norm_num

#print axioms clock_curvature_term_cannot_be_dropped
#print axioms equal_capacity_can_cover
#print axioms initial_transient_cannot_be_dropped
#print axioms endpoints_do_not_bound_remainder
#print axioms nonstrict_depth_margin_can_vanish
end FactoryNegativeControls
