import Mathlib.Tactic
namespace R02Domain
-- Literal source direct acceleration-command law; retained actual state is essential.
noncomputable def command (x v a q qv qa j : ℝ) : ℝ :=
  -800*x-60*v-(1/2)*a+800*q+60*qv+(3/2)*qa+j/96

theorem retained_state_jump (x v a q0 v0 a0 j0 q1 v1 a1 j1 : ℝ) :
    command x v a q1 v1 a1 j1-command x v a q0 v0 a0 j0 =
    800*(q1-q0)+60*(v1-v0)+(3/2)*(a1-a0)+(j1-j0)/96 := by
  unfold command; ring

theorem state_reset_correction (x0 v0 a0 x1 v1 a1 q0 w0 b0 j0 q1 w1 b1 j1 : ℝ) :
    command x1 v1 a1 q1 w1 b1 j1-command x0 v0 a0 q0 w0 b0 j0 =
    800*(q1-q0)+60*(w1-w0)+(3/2)*(b1-b0)+(j1-j0)/96
      -800*(x1-x0)-60*(v1-v0)-(1/2)*(a1-a0) := by
  unfold command; ring

theorem actual_jerk_jump (r u0 u1 w a : ℝ) :
    r*(u1+w-a)-r*(u0+w-a)=r*(u1-u0) := by ring

theorem jump_error_bound (dq dv da dj eq ev ea : ℝ)
    (hq : |dq| ≤ eq) (hv : |dv| ≤ ev) (ha : |da| ≤ ea) :
    |800*dq+60*dv+(3/2)*da+dj/96-dj/96| ≤ 800*eq+60*ev+(3/2)*ea := by
  have h := abs_add_le (800*dq+60*dv) ((3/2)*da)
  have h' := abs_add_le (800*dq) (60*dv)
  norm_num [abs_mul] at h h'
  rw [add_sub_cancel_right]
  nlinarith

theorem opposite_jumps (d : ℝ) : |d|+|-d|=2*|d| := by rw [abs_neg]; ring

theorem ledger_split (C A B : ℝ) : C+A+B = C+(A+B) := by ring

theorem ledger_omission (C A B : ℝ) (hB : 0 < B) : C+A < C+A+B := by linarith
theorem jump_mass_error (dq dv da dj eq ev ea : ℝ)
    (hq : |dq| ≤ eq) (hv : |dv| ≤ ev) (ha : |da| ≤ ea) :
    abs (abs (800*dq+60*dv+(3/2)*da+dj/96) - abs (dj/96)) ≤
       800*eq+60*ev+(3/2)*ea := by
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (jump_error_bound dq dv da dj eq ev ea hq hv ha)
end R02Domain
#print axioms R02Domain.retained_state_jump
#print axioms R02Domain.state_reset_correction
#print axioms R02Domain.actual_jerk_jump
#print axioms R02Domain.jump_error_bound
#print axioms R02Domain.opposite_jumps
#print axioms R02Domain.ledger_split
#print axioms R02Domain.ledger_omission

#print axioms R02Domain.jump_mass_error
