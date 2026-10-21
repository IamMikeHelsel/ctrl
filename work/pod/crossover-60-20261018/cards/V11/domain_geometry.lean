import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace V11Geometry
/-- Observation z=(1,0,0,0), rows(x,y,x+y,x+2y), at most one arbitrary outlier.
The union of all three-inlier branches, not a selected fitted branch, is quantified. -/
theorem all_branches_bound (x y e : ℝ) (he : 0 ≤ e) (hsmall : e < 1/4)
    (hworld :
      (|x-1| ≤ e ∧ |y| ≤ e ∧ |x+y| ≤ e) ∨
      (|x-1| ≤ e ∧ |y| ≤ e ∧ |x+2*y| ≤ e) ∨
      (|x-1| ≤ e ∧ |x+y| ≤ e ∧ |x+2*y| ≤ e) ∨
      (|y| ≤ e ∧ |x+y| ≤ e ∧ |x+2*y| ≤ e)) :
    |x| ≤ 2*e ∧ |y| ≤ e := by
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
  · rcases h234 with ⟨h2,h3,h4⟩
    refine ⟨?_,h2⟩
    have h2' := abs_le.mp h2
    have h3' := abs_le.mp h3
    apply abs_le.mpr
    constructor <;> linarith

/-- The coordinate bound cannot improve uniformly: this world fits rows 234. -/
theorem sharp_world (e : ℝ) (he : 0 ≤ e) :
    |(-e)| ≤ e ∧ |2*e+(-e)| ≤ e ∧ |2*e+2*(-e)| ≤ e ∧ |2*e|=2*e := by
  have hneg : |-e|=e := by rw [abs_neg, abs_of_nonneg he]
  have hpos : |e|=e := abs_of_nonneg he
  have hp : |2*e|=2*e := abs_of_nonneg (by linarith)
  constructor
  · exact hneg.le
  constructor
  · convert hpos.le using 1 <;> congr 1 <;> ring
  constructor
  · have hz : 2*e+2*(-e)=0 := by ring
    rw [hz,abs_zero]
    exact he
  · exact hp

/-- At e=1/4, another three-inlier branch appears and breaks the proposed x bound. -/
theorem threshold_failure :
    |(3/4:ℝ)-1| ≤ 1/4 ∧ |(-1/4:ℝ)| ≤ 1/4 ∧
    |(3/4:ℝ)+2*(-1/4)| ≤ 1/4 ∧
    2*(1/4:ℝ) < |(3/4:ℝ)| := by norm_num
#print axioms all_branches_bound
#print axioms sharp_world
#print axioms threshold_failure
end V11Geometry
