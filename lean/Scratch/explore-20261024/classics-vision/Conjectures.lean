import Mathlib

/-!
# Labelled CONJECTURES (sorry'd statements, not claimed proved)
-/

open Matrix

namespace ClassicsVisionConjectures

/-- CONJECTURE (Huang–Faugeras 1989 / Demazure 1988 converse): a nonzero real `3×3` matrix
with `det E = 0` and `2 E Eᵀ E - tr(E Eᵀ) E = 0` is an essential matrix `[t]ₓ R`, `R ∈ SO(3)`. -/
theorem huang_faugeras (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E ≠ 0) (hdet : E.det = 0)
    (hcubic : (2 : ℝ) • (E * Eᵀ * E) - trace (E * Eᵀ) • E = 0) :
    ∃ (R : Matrix (Fin 3) (Fin 3) ℝ) (t : Fin 3 → ℝ), Rᵀ * R = 1 ∧ R.det = 1 ∧
      E = !![0, -t 2, t 1; t 2, 0, -t 0; -t 1, t 0, 0] * R := by
  sorry

/-- CONJECTURE (Grunert 1841, "at most 4"): for fixed side lengths and bearing cosines with
non-collinear world points (may need strict triangle inequalities and
-- bearing-consistency hypotheses), Grunert's system has at most 4 positive-depth solutions. -/
theorem grunert_at_most_four (a b c α β γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hα : |α| < 1) (hβ : |β| < 1) (hγ : |γ| < 1) :
    Set.encard {d : Fin 3 → ℝ | (∀ i, 0 < d i) ∧
      a ^ 2 = d 1 ^ 2 + d 2 ^ 2 - 2 * d 1 * d 2 * α ∧
      b ^ 2 = d 0 ^ 2 + d 2 ^ 2 - 2 * d 0 * d 2 * β ∧
      c ^ 2 = d 0 ^ 2 + d 1 ^ 2 - 2 * d 0 * d 1 * γ} ≤ 4 := by
  sorry

end ClassicsVisionConjectures
