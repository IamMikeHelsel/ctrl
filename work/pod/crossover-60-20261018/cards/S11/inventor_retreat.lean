module
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace S11Inventor

/-- Boundary inequality only: no premise that the actual acceleration remains
above its initial value. `y` is the upper comparison barrier at a crossing. -/
theorem boundary_upper {A B r b y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) (hrhi : r ≤ 12)
    (hb : b ≤ B) (hy : -A ≤ y) :
    r * (b-y) ≤ 12 * (B+A) := by
  have hba : b-y ≤ B+A := by linarith
  have hp : r*(b-y) ≤ r*(B+A) := mul_le_mul_of_nonneg_left hba hr
  have hq : r*(B+A) ≤ 12*(B+A) :=
    mul_le_mul_of_nonneg_right hrhi (add_nonneg hB hA)
  exact hp.trans hq

/-- Arithmetic of integrating the affine barrier twice, conditional on the
already-established integrated upper bound. Not a formal ODE comparison. -/
theorem exact_retreat {displacement : ℝ}
    (h : displacement ≤ -(6/5 : ℝ)*(10/321)^2/2+(963/25)*(10/321)^3/6) :
    displacement ≤ -(40/103041 : ℝ) := by
  norm_num at h ⊢
  exact h

theorem time_and_slope :
    (12 : ℝ)*((201/100)+(6/5))=963/25 ∧
    (6/5 : ℝ)/(963/25)=10/321 ∧
    (3/10000 : ℝ)<40/103041 := by norm_num

#print axioms boundary_upper
#print axioms exact_retreat
#print axioms time_and_slope

/-- Critic improvement: minimize the integrated cubic upper bound at 2A/K.
The earlier theorem remains unchanged and independently valid. -/
theorem improved_exact_retreat {displacement : ℝ}
    (h : displacement ≤ -(6/5 : ℝ)*(20/321)^2/2+(963/25)*(20/321)^3/6) :
    displacement ≤ -(80/103041 : ℝ) := by
  norm_num at h ⊢
  exact h

theorem improved_velocity_upper_zero :
    -(6/5 : ℝ)*(20/321)+(963/25)*(20/321)^2/2=0 := by norm_num

#print axioms improved_exact_retreat
#print axioms improved_velocity_upper_zero

/-- Root's exponential-barrier arithmetic only; hE must come from an actual
exponential enclosure and h from a comparison/integration theorem. -/
theorem exponential_retreat_arithmetic {displacement E : ℝ}
    (hE : 367/1000 ≤ E)
    (h : displacement ≤ (201/100 : ℝ)/288-(321/100)*E/144) :
    displacement ≤ -(1923/1600000 : ℝ) := by linarith

#print axioms exponential_retreat_arithmetic
end S11Inventor
