import ControlsLean.Robotics.SO3Rodrigues
import Mathlib

open Matrix ControlsLean.Vision ControlsLean.Robotics

namespace RoboticsLieScratch

/-- **Euler's rotation theorem (eigenvalue form)**: every `R ∈ SO(3)` has `det (R - I) = 0`. -/
theorem det_sub_one_of_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) : (R - 1).det = 0 := by
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp hR
  have h1 : R * Rᵀ = 1 := (mem_orthogonalGroup_iff (Fin 3) ℝ).mp hO
  have key : (R - 1).det = -(R - 1).det := by
    calc (R - 1).det = (R * (1 - Rᵀ)).det := by rw [Matrix.mul_sub, h1, Matrix.mul_one]
      _ = (1 - Rᵀ).det := by rw [det_mul, hdet, one_mul]
      _ = (1 - R).det := by rw [← det_transpose, transpose_sub, transpose_one, transpose_transpose]
      _ = (-(R - 1)).det := by rw [neg_sub]
      _ = -(R - 1).det := by rw [det_neg]; simp; ring
  linarith

/-- Hence every rotation fixes a nonzero vector (an axis). -/
theorem exists_axis_of_SO3 {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R ∈ specialOrthogonalGroup (Fin 3) ℝ) : ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ R *ᵥ v = v := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr (det_sub_one_of_SO3 hR)
  refine ⟨v, hv0, ?_⟩
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv
  exact hv

/-- Improper orthogonal matrices need not have a fixed axis: `-I`. -/
theorem neg_one_no_axis : ((-1 : Matrix (Fin 3) (Fin 3) ℝ) - 1).det ≠ 0 := by
  simp [det_fin_three]; norm_num

/-- `rodrigues_mul_rodrigues` really needs the unit-axis hypothesis:
for `ω = 2 e₂`, `R(π/2) R(π/2) ≠ R(π)` (determinants 169 vs 49). -/
theorem rodrigues_mul_fails_nonunit :
    rodrigues ![0, 0, 2] (Real.pi / 2) * rodrigues ![0, 0, 2] (Real.pi / 2)
      ≠ rodrigues ![0, 0, 2] (Real.pi / 2 + Real.pi / 2) := by
  intro h
  have hd := congrArg Matrix.det h
  rw [det_mul, add_halves] at hd
  simp [rodrigues, det_fin_three, skew] at hd
  norm_num at hd

end RoboticsLieScratch
