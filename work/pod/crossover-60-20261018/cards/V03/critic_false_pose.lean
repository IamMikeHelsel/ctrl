import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- AI-written exact ambiguity certificate for ideal normalized pinhole cameras.
   Unknown scene plane may differ between reconstructions. Not an approved Challenge.
   All matrices and rays are explicit in statements; no source theorem is changed. -/
set_option autoImplicit false
open Matrix
namespace V03Planar

theorem alternative_rotation_proper :
    let R : Matrix (Fin 3) (Fin 3) ℝ :=
      !![3/5,0,4/5; 0,1,0; -4/5,0,3/5]
    Rᵀ * R = 1 ∧ R.det = 1 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem first_pose_matches (u v : ℝ) :
    ![u + 1, v, 1] = (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![u,v,1] + ![1,0,0] := by
  ext i
  fin_cases i <;> simp

theorem alternative_pose_matches (u v depth : ℝ)
    (plane_depth : depth * (2 * u + 1) = 1) :
    depth • ![u+1,v,1] =
      (!![3/5,0,4/5; 0,1,0; -4/5,0,3/5] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (depth • ![u,v,1]) + ![2/5,0,2/5] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> nlinarith

theorem positive_depth_exists (u : ℝ) (hu : -(1/2) < u) :
    ∃ depth : ℝ, 0 < depth ∧ depth * (2 * u + 1) = 1 := by
  have hden : 0 < 2 * u + 1 := by linarith
  refine ⟨(2*u+1)⁻¹, inv_pos.mpr hden, ?_⟩
  exact inv_mul_cancel₀ (ne_of_gt hden)

theorem common_rays_have_positive_third_coordinates (u v depth : ℝ) (hd : 0 < depth) :
    0 < (depth • (![u,v,1] : Fin 3 → ℝ)) 2 ∧
    0 < (depth • (![u+1,v,1] : Fin 3 → ℝ)) 2 := by
  simpa using And.intro hd hd

theorem rotations_distinct :
    (!![3/5,0,4/5; 0,1,0; -4/5,0,3/5] : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [Matrix.one_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this

theorem translations_not_same_direction :
    ¬ ∃ scale : ℝ, (![1/5,0,2/5] : Fin 3 → ℝ) = scale • ![1,0,0] := by
  rintro ⟨scale, h⟩
  have := congrFun h 2
  norm_num [Matrix.one_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this

theorem second_essential_is_skew_times_rotation :
    (!![0,-2/5,0; 2/5,0,1/5; 0,1/5,0] : Matrix (Fin 3) (Fin 3) ℝ) =
      !![0,-2/5,0; 2/5,0,-1/5; 0,1/5,0] *
        !![3/5,0,4/5; 0,1,0; -4/5,0,3/5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

theorem two_epipolar_constraints (u v : ℝ) :
    (![u+1,v,1] : Fin 3 → ℝ) ⬝ᵥ
      ((!![0,0,0; 0,0,-1; 0,1,0] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![u,v,1]) = 0 ∧
    (![u+1,v,1] : Fin 3 → ℝ) ⬝ᵥ
      ((!![0,-2/5,0; 2/5,0,1/5; 0,1/5,0] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ![u,v,1]) = 0 := by
  constructor <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem essential_matrices_not_proportional :
    ¬ ∃ scale : ℝ,
      (!![0,-2/5,0; 2/5,0,1/5; 0,1/5,0] : Matrix (Fin 3) (Fin 3) ℝ) =
        scale • !![0,0,0; 0,0,-1; 0,1,0] := by
  rintro ⟨scale, h⟩
  have := congrFun (congrFun h 0) 1
  norm_num [Matrix.one_apply, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this

#print axioms alternative_rotation_proper
#print axioms first_pose_matches
#print axioms alternative_pose_matches
#print axioms positive_depth_exists
#print axioms common_rays_have_positive_third_coordinates
#print axioms rotations_distinct
#print axioms translations_not_same_direction
#print axioms second_essential_is_skew_times_rotation
#print axioms two_epipolar_constraints
#print axioms essential_matrices_not_proportional
end V03Planar
