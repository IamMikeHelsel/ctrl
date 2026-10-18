module
public import LeanControls.Generated.TravelQuarterLower
@[expose] public section
noncomputable section
namespace LeanControls.TravelGeometry
open Matrix BernsteinCertificate
abbrev P := Generated.TravelQuarterLower.P
def positionResidual : Matrix (Fin 3) (Fin 3) ℝ := !![(23 / 15), (257 / 75), (5 / 3); (257 / 75), (1319 / 150), (769 / 150); (5 / 3), (769 / 150), (278 / 75)]
theorem positionResidual_psd : positionResidual.PosSemidef := by
  apply psd_of_ldl positionResidual !![1, 0, 0; (257 / 115), 1, 0; (25 / 23), (24185 / 19587), 1] ![(23 / 15), (6529 / 5750), (481607 / 2938050)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [positionResidual, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
def requestResidual : Matrix (Fin 3) (Fin 3) ℝ := !![(14 / 5), (107 / 50), (1 / 2); (107 / 50), (419 / 100), (169 / 100); (1 / 2), (169 / 100), (39 / 25)]
theorem requestResidual_psd : requestResidual.PosSemidef := by
  apply psd_of_ldl requestResidual !![1, 0, 0; (107 / 140), 1, 0; (5 / 28), (9155 / 17881), 1] ![(14 / 5), (17881 / 7000), (1432441 / 1788100)]
  · intro i; fin_cases i <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;> simp [requestResidual, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply, Matrix.diagonal, Matrix.of_apply, Matrix.vecHead, Matrix.vecTail] <;> norm_num
theorem position_energy (z : Fin 3 → ℝ) : (z 0)^2 ≤ energy P z / 3 := by
  have hp := positionResidual_psd.dotProduct_mulVec_nonneg z
  simp [positionResidual, energy, P, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at *
  nlinarith
theorem request_energy (z : Fin 3 → ℝ) : (-z 0 - 3*z 1 - 2*z 2)^2 ≤ energy P z / 2 := by
  have hp := requestResidual_psd.dotProduct_mulVec_nonneg z
  simp [requestResidual, energy, P, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at *
  nlinarith
theorem position_safe {z : Fin 3 → ℝ} (hz : energy P z ≤ 12) : |z 0| ≤ 2 := by
  have hp := position_energy z
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z 0 - 2), sq_nonneg (z 0 + 2)]
theorem sector_safe {z : Fin 3 → ℝ} (hz : energy P z ≤ 12) :
    (1/4:ℝ) * |(-z 0 - 3*z 1 - 2*z 2)| ≤ 1 := by
  have hp := request_energy z
  have ha := sq_abs (-z 0 - 3*z 1 - 2*z 2)
  have hn := abs_nonneg (-z 0 - 3*z 1 - 2*z 2)
  nlinarith
theorem active_initial_energy : energy P ![0,0,1] = 278/25 := by
  norm_num [energy, P, Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
end LeanControls.TravelGeometry
