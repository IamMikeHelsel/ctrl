import SplitSignature

noncomputable section
open Matrix
namespace HyperbolicSpinor

def Uc : CMatrix := realToComplexMatrix U
def Dc : CMatrix := realToComplexMatrix D
def Ucinverse : CMatrix := realToComplexMatrix Uinverse

theorem Uc_orthogonal_scaled : Uc.conjTranspose * Uc = (2 : ℂ) • (1 : CMatrix) := by
  have h := congrArg realToComplexMatrix U_orthogonal_scaled
  simpa only [map_mul, realToComplexMatrix_transpose, map_smul, map_one, Uc,
    two_smul, map_add] using h

theorem Uc_congruence : Uc.conjTranspose * Kc * Uc = (2 : ℂ) • Dc := by
  have h := congrArg realToComplexMatrix U_congruence
  simpa only [map_mul, realToComplexMatrix_transpose, map_smul, Uc, Kc, Dc,
    two_smul, map_add] using h

theorem Ucinverse_formula : Ucinverse = (1/2 : ℂ) • Uc.conjTranspose := by
  unfold Ucinverse Uinverse Uc
  rw [map_smul, realToComplexMatrix_transpose]
  ext I T
  simp [Matrix.smul_apply, Complex.real_smul]

theorem Ucinverse_left : Ucinverse * Uc = 1 := by
  rw [Ucinverse, Uc, ← map_mul, Uinverse_left, map_one]

theorem Ucinverse_right : Uc * Ucinverse = 1 := by
  rw [Ucinverse, Uc, ← map_mul, Uinverse_right, map_one]

theorem Dc_entry (I T : Finset J) :
    Dc I T = if I = T then (if (0 : J) ∈ T then (-1 : ℂ) else 1) else 0 := by
  by_cases h : I = T
  · subst T
    by_cases hm : (0 : J) ∈ I <;> simp [Dc, D, halfSign, hm]
  · simp [Dc, D, Matrix.diagonal_apply, h]

theorem Uc_congruence_entry (I T : Finset J) :
    (Uc.conjTranspose * Kc * Uc) I T =
      if I = T then (if (0 : J) ∈ T then (-2 : ℂ) else 2) else 0 := by
  rw [Uc_congruence, Matrix.smul_apply, Dc_entry]
  split_ifs <;> norm_num

end HyperbolicSpinor
