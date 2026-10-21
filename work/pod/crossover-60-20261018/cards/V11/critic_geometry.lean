import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace V11Critic
-- Conditional linear certificate: two shared inlier rows among x,y,x+y,x+2y.
theorem two_common_rows_bound (x y e : ℝ) (he : 0 ≤ e)
    (hp : (|x|≤2*e ∧ |y|≤2*e) ∨
          (|x|≤2*e ∧ |x+y|≤2*e) ∨
          (|x|≤2*e ∧ |x+2*y|≤2*e) ∨
          (|y|≤2*e ∧ |x+y|≤2*e) ∨
          (|y|≤2*e ∧ |x+2*y|≤2*e) ∨
          (|x+y|≤2*e ∧ |x+2*y|≤2*e)) :
    |x|≤6*e ∧ |y|≤4*e := by
  rcases hp with hp | hp | hp | hp | hp | hp <;>
    rcases abs_le.mp hp.1 with ⟨hl,hu⟩ <;>
    rcases abs_le.mp hp.2 with ⟨kl,ku⟩ <;>
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith

-- Observations(0,-4e,e,-e), worlds A=(0,0),B=(6e,-4e).
theorem sharp_pair (e : ℝ) (he : 0 ≤ e) :
    |(6*e + (-4*e))-e|≤e ∧
    |(6*e + 2*(-4*e))-(-e)|≤e ∧
    |6*e-0|=6*e ∧ |(-4*e)-0|=4*e := by
  have h6 : 0 ≤ 6*e := by linarith
  have h4 : 0 ≤ 4*e := by linarith
  constructor
  · have hh : 6*e + (-4*e)-e=e := by ring
    rw [hh,abs_of_nonneg he]
  constructor
  · have hh : 6*e+2*(-4*e)-(-e) = -e := by ring
    rw [hh,abs_neg,abs_of_nonneg he]
  constructor
  · simpa using abs_of_nonneg h6
  · have hh : (-4*e)-0=-(4*e) := by ring
    rw [hh,abs_neg,abs_of_nonneg h4]
#print axioms two_common_rows_bound
#print axioms sharp_pair
end V11Critic
