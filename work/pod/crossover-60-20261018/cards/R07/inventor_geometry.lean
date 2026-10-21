import Mathlib.Tactic

namespace R07Inventor
noncomputable section

def task (x y : ℝ) : ℝ := x^2+y^2
def cx (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
def cy (t : ℝ) : ℝ := 2*t/(1+t^2)

theorem denominator_positive (t : ℝ) : 0 < 1+t^2 := by positivity

theorem cayley_task (t : ℝ) : task (cx t) (cy t)=1 := by
  have hd : 1+t^2 ≠ 0 := ne_of_gt (denominator_positive t)
  unfold task cx cy
  field_simp
  ring

theorem left_cayley_task (t : ℝ) : task (-cx t) (cy t)=1 := by
  simpa [task] using cayley_task t

theorem safe_left (t : ℝ) (ht : -1 ≤ t ∧ t ≤ 1) : -cx t ≤ 4/5 := by
  have hp : 0 ≤ (1-t)*(1+t) := mul_nonneg (by linarith) (by linarith)
  have hn : 0 ≤ 1-t^2 := by nlinarith
  have hc : 0 ≤ cx t := div_nonneg hn (denominator_positive t).le
  linarith

theorem endpoints_and_bad_midpoint :
    cx (-1)=0 ∧ cy (-1) = -1 ∧ cx 1=0 ∧ cy 1=1 ∧ 4/5 < cx 0 := by
  norm_num [cx,cy]

theorem singular_fiber (x y : ℝ) (h : task x y=0) : x=0 ∧ y=0 := by
  unfold task at h
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

theorem linearized_not_finite :
    (2*(0:ℝ)*(1/10)+2*0*0=0) ∧ task (1/10) 0 ≠ task 0 0 := by
  norm_num [task]

theorem regular_euler_drift : task 1 (1/10)=101/100 := by norm_num [task]

/-- Conditional curvature equation: it must be derived from the actual
second derivative of the task, not assumed for an arbitrary physical plant. -/
theorem curvature_budget (a1 a2 : ℝ)
    (hpreserve : (1/100)*a1+0*a2 = -(1/5 : ℝ)^2) : a1 = -4 := by
  linarith

theorem curvature_infeasible (a1 a2 : ℝ)
    (hpreserve : (1/100)*a1+0*a2 = -(1/5 : ℝ)^2)
    (hactuator : a1^2+a2^2 ≤ 1) : False := by
  have ha := curvature_budget a1 a2 hpreserve
  rw [ha] at hactuator
  nlinarith [sq_nonneg a2]

/-- Same task's obstacle-separated fiber has no point on the separating axis.
The continuous-path IVT bridge is not formalized in this lemma. -/
theorem forbidden_axis (y : ℝ) (htask : task 0 y=1) (hobs : |y| ≤ 3/5) : False := by
  have hb := abs_le.mp hobs
  unfold task at htask
  have hp : 0 ≤ (3/5-y)*(3/5+y) := mul_nonneg (by linarith) (by linarith)
  nlinarith

#print axioms cayley_task
#print axioms left_cayley_task
#print axioms safe_left
#print axioms endpoints_and_bad_midpoint
#print axioms singular_fiber
#print axioms linearized_not_finite
#print axioms regular_euler_drift
#print axioms curvature_budget
#print axioms curvature_infeasible
#print axioms forbidden_axis
end
end R07Inventor
