import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/- Extra observations for the two explicit V03 poses; not a generic uniqueness theorem. -/
set_option autoImplicit false
open Matrix
namespace V03OffPlane

theorem alternative_residual (u v parallax : ℝ) :
    (![u+parallax,v,1] : Fin 3 → ℝ) ⬝ᵥ
      ((!![0,-2/5,0; 2/5,0,1/5; 0,1/5,0] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ![u,v,1]) = (2/5)*v*(1-parallax) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem offplane_point_rejects_alternative :
    (![1/2,1/2,1] : Fin 3 → ℝ) ⬝ᵥ
      ((!![0,-2/5,0; 2/5,0,1/5; 0,1/5,0] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ![0,1/2,1]) = 1/10 := by
  calc
    _ = (2/5 : ℝ)*(1/2)*(1-(1/2)) := by
      simpa only [zero_add] using alternative_residual 0 (1/2) (1/2)
    _ = 1/10 := by norm_num

theorem failure_line (u parallax : ℝ) :
    (![u+parallax,0,1] : Fin 3 → ℝ) ⬝ᵥ
      ((!![0,-2/5,0; 2/5,0,1/5; 0,1/5,0] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ![u,0,1]) = 0 := by
  simpa using alternative_residual u 0 parallax

theorem observation_has_positive_depth_pose_a :
    (2 : ℝ) • (![1/2,1/2,1] : Fin 3 → ℝ) =
      2 • (![0,1/2,1] : Fin 3 → ℝ) + ![1,0,0] := by
  ext i
  fin_cases i <;> norm_num

#print axioms alternative_residual
#print axioms offplane_point_rejects_alternative
#print axioms failure_line
#print axioms observation_has_positive_depth_pose_a
end V03OffPlane
