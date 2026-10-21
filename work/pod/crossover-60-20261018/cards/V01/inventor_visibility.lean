import Mathlib

namespace V01Visibility

/-- Restrict rays to the nonzero optical-axis family z*e3. A predicate invariant
under the projective sign identification cannot classify positive physical depth. -/
theorem no_sign_invariant_visibility (P : ℝ → Prop)
    (hscale : ∀ z : ℝ, z ≠ 0 → (P (-z) ↔ P z))
    (hvisible : ∀ z : ℝ, z ≠ 0 → (P z ↔ 0 < z)) : False := by
  have hp : P 1 := (hvisible 1 (by norm_num)).2 (by norm_num)
  have hn : P (-1) := (hscale 1 (by norm_num)).2 hp
  have hh : (0:ℝ) < -1 := (hvisible (-1) (by norm_num)).1 hn
  norm_num at hh

/-- A known representative gauge restores the canonical height exactly. -/
theorem gauge_height (α height : ℝ) (ha : α ≠ 0) :
    (α*height)/α = height := by field_simp

end V01Visibility
#print axioms V01Visibility.no_sign_invariant_visibility
#print axioms V01Visibility.gauge_height
