import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace R07InventorTiming
noncomputable section

def phase (z : ℝ) : ℝ := 2*(10*z^3-15*z^4+6*z^5)-1
def phaseD (z : ℝ) : ℝ := 60*z^2*(1-z)^2
def phaseDD (z : ℝ) : ℝ := 120*z*(1-z)*(1-2*z)

theorem phase_derivative (z : ℝ) : HasDerivAt phase (phaseD z) z := by
  have h := (((((hasDerivAt_id z).pow 3).const_mul 10).sub
    (((hasDerivAt_id z).pow 4).const_mul 15)).add
    (((hasDerivAt_id z).pow 5).const_mul 6)).const_mul 2
  have hh := h.sub_const 1
  have hh' : HasDerivAt phase (2*(10*(3*z^2)-15*(4*z^3)+6*(5*z^4))) z := by
    change HasDerivAt (fun x : ℝ => 2*(10*x^3-15*x^4+6*x^5)-1) _ z
    simpa using hh
  have he : 2*(10*(3*z^2)-15*(4*z^3)+6*(5*z^4))=phaseD z := by
    unfold phaseD
    ring
  rwa [he] at hh'

theorem phase_second_derivative (z : ℝ) : HasDerivAt phaseD (phaseDD z) z := by
  have h := (((hasDerivAt_id z).pow 2).mul
    (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).pow 2)).const_mul 60
  have h' : HasDerivAt phaseD (60*(2*z*(1-z)^2+z^2*(2*(1-z)*(-1)))) z := by
    change HasDerivAt (fun x : ℝ => 60*x^2*(1-x)^2) _ z
    simpa [mul_assoc] using h
  have he : 60*(2*z*(1-z)^2+z^2*(2*(1-z)*(-1)))=phaseDD z := by
    unfold phaseDD
    ring
  rwa [he] at h'

theorem phase_range (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1) : -1 ≤ phase z ∧ phase z ≤ 1 := by
  have hz0 : 0 ≤ z := hz.1
  have hzm : 0 ≤ 1-z := by linarith
  have hlow : 0 ≤ z^3*(1+3*(1-z)+6*(1-z)^2) := by positivity
  have hhigh : 0 ≤ (1-z)^3*(1+3*z+6*z^2) := by positivity
  have hlo : phase z+1=2*(z^3*(1+3*(1-z)+6*(1-z)^2)) := by unfold phase; ring
  have hhi : 1-phase z=2*((1-z)^3*(1+3*z+6*z^2)) := by unfold phase; ring
  constructor <;> linarith

theorem phase_velocity_bound (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ phaseD z ∧ phaseD z ≤ 15/4 := by
  have hw : 0 ≤ z*(1-z) := mul_nonneg hz.1 (by linarith)
  have hm : z*(1-z) ≤ 1/4 := by nlinarith [sq_nonneg (z-1/2)]
  have hp : 0 ≤ (1/4-z*(1-z))*(1/4+z*(1-z)) :=
    mul_nonneg (by linarith) (by linarith)
  have he : phaseD z=60*(z*(1-z))^2 := by unfold phaseD; ring
  rw [he]
  constructor <;> nlinarith [sq_nonneg (z*(1-z))]

theorem phase_acceleration_bound (z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1) : |phaseDD z| ≤ 30 := by
  have hw : 0 ≤ z*(1-z) := mul_nonneg hz.1 (by linarith)
  have hm : z*(1-z) ≤ 1/4 := by nlinarith [sq_nonneg (z-1/2)]
  have ha : |1-2*z| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have he : phaseDD z=(120*(z*(1-z)))*(1-2*z) := by unfold phaseDD; ring
  rw [he,abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hw)]
  calc
    120*(z*(1-z))*|1-2*z| ≤ 120*(z*(1-z))*1 :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num) hw)
    _ ≤ 30 := by nlinarith

theorem endpoints : phase 0 = -1 ∧ phase 1 = 1 ∧ phaseD 0=0 ∧ phaseD 1=0 ∧
    phaseDD 0=0 ∧ phaseDD 1=0 := by norm_num [phase,phaseD,phaseDD]

/-- Conditional chain-rule norm arithmetic; geometric norm bounds and the
physical model must be supplied separately. -/
theorem T12_norm_budget (speed acceleration : ℝ)
    (hv : speed ≤ 2*((15/4)/12 : ℝ))
    (ha : acceleration ≤ 4*((15/4)/12 : ℝ)^2+2*(30/12^2)) :
    speed ≤ 5/8 ∧ acceleration ≤ 155/192 ∧ acceleration < 1 := by
  constructor
  · norm_num at hv ⊢; exact hv
  constructor
  · norm_num at ha ⊢; exact ha
  · norm_num at ha; linarith

#print axioms phase_derivative
#print axioms phase_second_derivative
#print axioms phase_range
#print axioms phase_velocity_bound
#print axioms phase_acceleration_bound
#print axioms endpoints
#print axioms T12_norm_budget
end
end R07InventorTiming
