import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace V11Geometry
/-- Actual surviving observation bounds, suitable for the admission interface.
This returns all three bounds instead of only an outer box on the state. -/
theorem certified_survivors (x y e : ℝ) (hsmall : e < 1/4)
    (hworld :
      (|x-1| ≤ e ∧ |y| ≤ e ∧ |x+y| ≤ e) ∨
      (|x-1| ≤ e ∧ |y| ≤ e ∧ |x+2*y| ≤ e) ∨
      (|x-1| ≤ e ∧ |x+y| ≤ e ∧ |x+2*y| ≤ e) ∨
      (|y| ≤ e ∧ |x+y| ≤ e ∧ |x+2*y| ≤ e)) :
    |y| ≤ e ∧ |x+y| ≤ e ∧ |x+2*y| ≤ e := by
  rcases hworld with h123 | h124 | h134 | h234
  · rcases h123 with ⟨h1,h2,h3⟩
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    have h3' := abs_le.mp h3
    exfalso
    linarith
  · rcases h124 with ⟨h1,h2,h4⟩
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    have h4' := abs_le.mp h4
    exfalso
    linarith
  · rcases h134 with ⟨h1,h3,h4⟩
    have h1' := abs_le.mp h1
    have h3' := abs_le.mp h3
    have h4' := abs_le.mp h4
    exfalso
    linarith
  · exact h234
#print axioms certified_survivors
end V11Geometry
