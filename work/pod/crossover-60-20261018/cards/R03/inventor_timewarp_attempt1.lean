import Mathlib

noncomputable section
namespace R03Timewarp
open Set

/- The actual source's four-box position kernel on phase z∈[1,2], multiplied
by its saved event amplitude1/50. Physical time is centered at103/200. -/
def branch (rate t : ℝ) : ℝ :=
  ((3/2+5*rate*t)^4-4*(3/2+5*rate*t-1)^4)/1200
def warped (t : ℝ) : ℝ := if t≤0 then branch (3/2) t else branch (1/2) t

theorem branch_derivative (rate : ℝ) :
    HasDerivAt (branch rate) (23/480*rate) 0 := by
  have ha : HasDerivAt (fun t : ℝ => 3/2+5*rate*t) (5*rate) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul (5*rate)).const_add (3/2)
  have hb := ((ha.pow 4).sub (((ha.sub_const 1).pow 4).const_mul 4)).div_const 1200
  convert hb using 1 <;> norm_num [branch] <;> ring

theorem branches_join : branch (3/2) 0 = branch (1/2) 0 := by norm_num [branch]

theorem left_derivative : HasDerivAt (branch (3/2)) (23/320) 0 := by
  convert branch_derivative (3/2) using 1 <;> norm_num

theorem right_derivative : HasDerivAt (branch (1/2)) (23/960) 0 := by
  convert branch_derivative (1/2) using 1 <;> norm_num

theorem clock_evaluated_reference_not_differentiable :
    ¬ DifferentiableAt ℝ warped 0 := by
  have hl : HasDerivWithinAt warped (23/320) (Iic 0) 0 := by
    apply left_derivative.hasDerivWithinAt.congr
    · intro t ht
      change t≤0 at ht
      simp [warped, ht]
    · simp [warped]
  have hr : HasDerivWithinAt warped (23/960) (Ici 0) 0 := by
    apply right_derivative.hasDerivWithinAt.congr
    · intro t ht
      by_cases ht0 : t≤0
      · have ht' : t=0 := le_antisymm ht0 ht
        subst t
        simpa [warped] using branches_join
      · simp [warped, ht0]
    · simpa [warped] using branches_join
  intro hd
  have el := UniqueDiffWithinAt.eq_deriv (Iic 0) (uniqueDiffWithinAt_Iic 0)
    hl hd.hasDerivAt.hasDerivWithinAt
  have er := UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffWithinAt_Ici 0)
    hr hd.hasDerivAt.hasDerivWithinAt
  linarith

theorem velocity_jump : (23:ℝ)/960-23/320 = -23/480 := by norm_num

theorem naive_clock_order_false_positive :
    (123:ℚ)/200+1/100≤5/8 ∧
    ¬ ((123:ℚ)/200+1/200+1/100≤5/8-1/200) ∧
    (31:ℚ)/50+1/100>31/50 := by norm_num

end R03Timewarp
#print axioms R03Timewarp.branch_derivative
#print axioms R03Timewarp.branches_join
#print axioms R03Timewarp.left_derivative
#print axioms R03Timewarp.right_derivative
#print axioms R03Timewarp.clock_evaluated_reference_not_differentiable
#print axioms R03Timewarp.velocity_jump
#print axioms R03Timewarp.naive_clock_order_false_positive
