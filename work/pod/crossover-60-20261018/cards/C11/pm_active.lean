import Mathlib
namespace C11Active
theorem facetwise_exact {X I : Type*} (P : X → Prop) (F : I → X → ℝ) (R : ℝ) :
    (∀ x, P x → ∀ i, F i x ≤ R) ↔ (∀ i x, P x → F i x ≤ R) := by
  constructor
  · intro h i x hx; exact h x hx i
  · intro h x hx i; exact h i x hx

theorem tied_active_max (t : ℝ) (ht : 0 ≤ t) : max (1-t) (1+t) = 1+t := by
  apply max_eq_right; linarith

theorem one_active_inward_insufficient (t : ℝ) (ht : 0 < t) :
    1-t < 1 ∧ 1 < max (1-t) (1+t) := by
  rw [tied_active_max t ht.le]; constructor <;> linarith

theorem same_time_obstruction :
    ¬ (∃ x : ℝ, x=1 ∧ -x=1) ∧ (max (1:ℝ) (-1) > 1/2) := by
  constructor
  · rintro ⟨x,h1,h2⟩; linarith
  · norm_num
#print axioms facetwise_exact
#print axioms tied_active_max
#print axioms one_active_inward_insufficient
#print axioms same_time_obstruction
end C11Active
