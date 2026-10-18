module

public import Mathlib.Tactic

/-!
# Three small, complete Lean proofs

Read the statement before the proof. Lean checks exactly that statement.
These are familiar mathematical facts, not claims of new research.
-/

public section
namespace LeanControls.Examples

/-- BASIC: expand a square, for every real number. -/
theorem square_expansion (x : ℝ) :
    (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  ring

/-- BASIC WITH A HYPOTHESIS: order is preserved by adding the same number. -/
theorem add_preserves_order (x y : ℝ) (h : x ≤ y) :
    x + 3 ≤ y + 3 := by
  linarith

/-- INTERMEDIATE: a stable scalar step makes the quadratic energy decrease. -/
theorem scalar_energy_decreases (a x : ℝ) (ha : |a| ≤ 1) :
    (a * x) ^ 2 ≤ x ^ 2 := by
  have ha_bounds : -1 ≤ a ∧ a ≤ 1 := abs_le.mp ha
  have ha_squared : a ^ 2 ≤ 1 := by
    nlinarith [ha_bounds.1, ha_bounds.2]
  have hx_squared : 0 ≤ x ^ 2 := sq_nonneg x
  calc
    (a * x) ^ 2 = a ^ 2 * x ^ 2 := by ring
    _ ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right ha_squared hx_squared
    _ = x ^ 2 := by ring

/-- INTERMEDIATE: a one-step error budget proves safety for every time step. -/
theorem stays_in_bound (V : ℕ → ℝ)
    (h_initial : V 0 ≤ 1)
    (h_step : ∀ n, V (n + 1) ≤ (9 / 10) * V n + 1 / 10) :
    ∀ n, V n ≤ 1 := by
  intro n
  induction n with
  | zero =>
      exact h_initial
  | succ n ih =>
      have h_next := h_step n
      linarith

end LeanControls.Examples
