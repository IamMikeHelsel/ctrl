import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/- Concrete positive-depth extra observations compatible with both V03 poses.
   The distinct-feature example avoids reusing an image ray from the saved9-point grid.
   Not a general characterization of critical configurations. -/
set_option autoImplicit false
open Matrix
namespace V03Nonplanar

theorem axial_extra_pose_a :
    (3/2 : ℝ) • (![2/3,0,1] : Fin 3 → ℝ) =
      (3/2 : ℝ) • (![0,0,1] : Fin 3 → ℝ) + ![1,0,0] := by
  ext i
  fin_cases i <;> norm_num

theorem axial_extra_pose_b :
    (1/2 : ℝ) • (![2/3,0,1] : Fin 3 → ℝ) =
      (!![3/5,0,4/5;0,1,0;-4/5,0,3/5] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ((1/6 : ℝ) • ![0,0,1]) + ![1/5,0,2/5] := by
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem distinct_extra_pose_a :
    (3/2 : ℝ) • (![11/12,0,1] : Fin 3 → ℝ) =
      (3/2 : ℝ) • (![1/4,0,1] : Fin 3 → ℝ) + ![1,0,0] := by
  ext i
  fin_cases i <;> norm_num

theorem distinct_extra_pose_b :
    (18/35 : ℝ) • (![11/12,0,1] : Fin 3 → ℝ) =
      (!![3/5,0,4/5;0,1,0;-4/5,0,3/5] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ((2/7 : ℝ) • ![1/4,0,1]) + ![1/5,0,2/5] := by
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem depths_positive_and_extra_points_off_planes :
    (0 : ℝ) < 3/2 ∧ (0 : ℝ) < 1/6 ∧ (0 : ℝ) < 1/2 ∧
    (0 : ℝ) < 2/7 ∧ (0 : ℝ) < 18/35 ∧
    (3/2 : ℝ) ≠ 1 ∧ (1/6 : ℝ) ≠ 1 ∧
    (2*(2/7)*(1/4)+(2/7) : ℝ) ≠ 1 := by norm_num

/-- Determinants of three displacement vectors from one retained grid point.
    A uses(0,0,1),(1/2,0,1),(0,1/2,1),(3/8,0,3/2).
    B uses(0,0,1),(1/4,0,1/2),(0,1/2,1),(1/14,0,2/7). -/
theorem affine_volume_witnesses_nonzero :
    (!![1/2,0,0;0,1/2,0;3/8,0,1/2] : Matrix (Fin 3) (Fin 3) ℝ).det = 1/8 ∧
    (!![1/4,0,-1/2;0,1/2,0;1/14,0,-5/7] : Matrix (Fin 3) (Fin 3) ℝ).det = -(1/14) := by
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

#print axioms axial_extra_pose_a
#print axioms axial_extra_pose_b
#print axioms distinct_extra_pose_a
#print axioms distinct_extra_pose_b
#print axioms depths_positive_and_extra_points_off_planes
#print axioms affine_volume_witnesses_nonzero
end V03Nonplanar
