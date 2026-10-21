import Mathlib.Tactic
namespace R02Inventor

noncomputable def step (s : ℝ × ℝ × ℝ) (j h : ℝ) : ℝ × ℝ × ℝ :=
  (s.1+s.2.1*h+s.2.2*h^2/2+j*h^3/6, s.2.1+s.2.2*h+j*h^2/2, s.2.2+j*h)

noncomputable def hidden (j h : ℝ) : ℝ × ℝ × ℝ :=
  step (step (step (step (0,0,0) j h) (-3*j) h) (3*j) h) (-j) h

theorem returns_to_rest (j h : ℝ) : hidden j h = (0,0,0) := by
  simp only [hidden, step, Prod.mk.injEq]
  constructor
  · ring
  constructor <;> ring

theorem first_phase_nonzero (j h : ℝ) (hj : 0 < j) (hh : 0 < h) :
    0 < (step (0,0,0) j h).2.2 := by
  simp only [step]
  positivity

theorem jerk_jump_variation (j : ℝ) (hj : 0 ≤ j) :
    |j| + |-4*j| + |6*j| + |-4*j| + |j| = 16*j := by
  rw [abs_of_nonneg hj, abs_of_nonpos (by linarith : -4*j ≤ 0),
      abs_of_nonneg (by positivity : 0 ≤ 6*j)]
  ring

theorem diagnostic_command_jump : (16*(5/2:ℝ))/96 = 5/12 := by norm_num
end R02Inventor
#print axioms R02Inventor.returns_to_rest
#print axioms R02Inventor.first_phase_nonzero
#print axioms R02Inventor.jerk_jump_variation
#print axioms R02Inventor.diagnostic_command_jump
