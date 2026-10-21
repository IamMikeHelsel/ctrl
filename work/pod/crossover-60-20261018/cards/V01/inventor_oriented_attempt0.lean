import Mathlib

/- Independent rational fixtures, not a replay of notebook Lean4.36 source. -/
namespace V01Inventor
open Matrix

def piR : Matrix (Fin 3) (Fin 3) ℚ := !![-1,0,0; 0,1,0; 0,0,-1]
def quarterR : Matrix (Fin 3) (Fin 3) ℚ := !![0,0,1; 0,1,0; -1,0,0]
def H : Matrix (Fin 3) (Fin 3) ℚ := !![1,0,1/2; 0,1,1; 0,0,5/2]
def Hp : Matrix (Fin 3) (Fin 3) ℚ := !![-1/2,0,1; 1,1,0; -5/2,0,0]

theorem rotations_orthogonal :
    piR.transpose*piR=1 ∧ quarterR.transpose*quarterR=1 := by decide

theorem rotations_proper : piR.det=1 ∧ quarterR.det=1 := by
  norm_num [piR, quarterR, Matrix.det_fin_three]

theorem reversed_ray :
    piR *ᵥ ![(1:ℚ)/2,0,1] = ![-1/2,0,-1] ∧
    ((-1:ℚ)/2)/(-1) = 1/2 := by decide

theorem horizon_action (u v : ℚ) :
    quarterR *ᵥ ![u,v,1] = ![1,v,-u] := by
  ext i
  fin_cases i <;> simp [quarterR, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem horizon_nonzero :
    quarterR *ᵥ ![(0:ℚ),2/3,1] = ![1,2/3,0] ∧
    (![(1:ℚ),2/3,0] : Fin 3 → ℚ) ≠ 0 := by decide

theorem oriented_guard_negative :
    ![(-1:ℚ),0,-1/10] ⬝ᵥ ![1/10,0,1] < 0 ∧
    ![(-1:ℚ)/10,0,1] ⬝ᵥ ![-10,0,1] > 0 := by decide

theorem passive_covariance : Hp = piR * H * quarterR.transpose := by decide

theorem passive_depth :
    quarterR *ᵥ ![(2:ℚ),1,2] = ![2,1,-2] ∧
    ![(1:ℚ),0,0] ⬝ᵥ ![2,1,-2] = 2 ∧
    ![(0:ℚ),0,1] ⬝ᵥ ![2,1,-2] = -2 ∧
    Hp *ᵥ ![(2:ℚ),1,-2] = ![-3,3,-5] := by decide

end V01Inventor
#print axioms V01Inventor.rotations_orthogonal
#print axioms V01Inventor.rotations_proper
#print axioms V01Inventor.reversed_ray
#print axioms V01Inventor.horizon_action
#print axioms V01Inventor.horizon_nonzero
#print axioms V01Inventor.oriented_guard_negative
#print axioms V01Inventor.passive_covariance
#print axioms V01Inventor.passive_depth
