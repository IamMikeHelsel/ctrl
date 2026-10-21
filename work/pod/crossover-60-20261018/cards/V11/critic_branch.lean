import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace V11CriticBranch
-- Exhaustive four branches for at most one arbitrary faulty row.
theorem only_good_branch (x y : ℝ)
    (h : (|y|≤1/100 ∧ |x+y|≤1/100 ∧ |x+2*y|≤1/100) ∨
      (|x-1|≤1/100 ∧ |x+y|≤1/100 ∧ |x+2*y|≤1/100) ∨
      (|x-1|≤1/100 ∧ |y|≤1/100 ∧ |x+2*y|≤1/100) ∨
      (|x-1|≤1/100 ∧ |y|≤1/100 ∧ |x+y|≤1/100)) :
    |y|≤1/100 ∧ |x+y|≤1/100 ∧ |x+2*y|≤1/100 := by
  rcases h with h | h | h | h
  · exact h
  all_goals
    have h1 := abs_le.mp h.1
    have h2 := abs_le.mp h.2.1
    have h3 := abs_le.mp h.2.2
    exfalso
    linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem sharp_radius_bound (x y : ℝ) (hy : |y|≤1/100) (hs : |x+y|≤1/100) :
    |x|≤1/50 ∧ |y|≤1/100 := by
  have h1 := abs_le.mp hy
  have h2 := abs_le.mp hs
  exact ⟨abs_le.mpr ⟨by linarith [h1.2,h2.1],by linarith [h1.1,h2.2]⟩,hy⟩

theorem extremal_world_and_bad_candidate :
    |(1:ℝ)/100|≤1/100 ∧ |(-1:ℝ)/50+1/100|≤1/100 ∧
    |(-1:ℝ)/50+2*(1/100)|≤1/100 ∧
    |(-1:ℝ)/50|=1/50 ∧
    |(17500:ℝ)/17503-(-1/50)|=(892503:ℝ)/875150 ∧
    (1:ℝ)<892503/875150 := by norm_num
#print axioms only_good_branch
#print axioms sharp_radius_bound
#print axioms extremal_world_and_bad_candidate
end V11CriticBranch
