import Mathlib.Tactic
namespace R02Pulse
noncomputable def step (q v a j h : ℝ) : ℝ × ℝ × ℝ :=
 (q+v*h+a*h^2/2+j*h^3/6,v+a*h+j*h^2/2,a+j*h)
noncomputable def next (z : ℝ × ℝ × ℝ) (j h : ℝ) := step z.1 z.2.1 z.2.2 j h

theorem rest_shift (j h : ℝ) : next (next (step 0 0 0 j h) (-j) (2*h)) j h =
 (2*j*h^3,0,0) := by ext <;> simp [next,step] <;> ring

theorem invisible_pulse (j h : ℝ) :
 next (next (next (step 0 0 0 j h) (-3*j) h) (3*j) h) (-j) h = (0,0,0) := by
 ext <;> simp [next,step] <;> ring

theorem pulse_midpoint (j h : ℝ) : next (step 0 0 0 j h) (-3*j) h =
 ((2/3)*j*h^3,0,-2*j*h) := by ext <;> simp [next,step] <;> ring

theorem command_jump (q v a j x xd xa dq dv da dj : ℝ) :
 (800*((q+dq)-x)+60*((v+dv)-xd)+(3/2)*(a+da)-(1/2)*xa+(j+dj)/96)-
 (800*(q-x)+60*(v-xd)+(3/2)*a-(1/2)*xa+j/96) =
 800*dq+60*dv+(3/2)*da+dj/96 := by ring

theorem pulse_variation (j : ℝ) (hj : 0≤j) :
 |j|+|(-3*j)-j|+|(3*j)-(-3*j)|+|(-j)-(3*j)|+|0-(-j)|=16*j := by
 rw [abs_of_nonneg hj,abs_of_nonpos (by linarith : -3*j-j≤0),
  abs_of_nonneg (by linarith : 0≤3*j-(-3*j)),
  abs_of_nonpos (by linarith : -j-3*j≤0),abs_of_nonneg (by linarith : 0≤0-(-j))]
 ring

theorem bounded_pulse_numbers :
 (3*(5/2):ℝ)=15/2 ∧ (16*(5/2)/96:ℝ)=5/12 ∧
 ((5/2)^2+(-3*(5/2))^2+(3*(5/2))^2+(-(5/2))^2:ℝ)=125 := by norm_num

theorem arbitrarily_small_energy (tol : ℝ) (ht : 0<tol) :
 0<tol/250 ∧ 125*(tol/250)<tol := by constructor <;> linarith
end R02Pulse
#print axioms R02Pulse.rest_shift
#print axioms R02Pulse.invisible_pulse
#print axioms R02Pulse.pulse_midpoint
#print axioms R02Pulse.command_jump
#print axioms R02Pulse.pulse_variation
#print axioms R02Pulse.bounded_pulse_numbers
#print axioms R02Pulse.arbitrarily_small_energy
