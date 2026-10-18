import ComplexEquivalence
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

noncomputable section
open scoped TensorProduct
namespace HyperbolicSpinor
open GUClifford GUComplex

/-- The complex form is the entrywise extension of the actual ordered product. -/
def Kc : CMatrix := realToComplexMatrix K

theorem realToComplexMatrix_transpose (A : SpinMatrix) :
    realToComplexMatrix A.transpose = (realToComplexMatrix A).conjTranspose := by
  ext I T
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

@[simp] theorem Kc_conjTranspose : Kc.conjTranspose = Kc := by
  rw [Kc, ← realToComplexMatrix_transpose, K_transpose]

@[simp] theorem Kc_square : Kc * Kc = 1 := by
  rw [Kc, ← map_mul, K_square, map_one]

theorem complexMatrixEquiv_bar_tmul (z : ℂ) (a : Cl) :
    complexMatrixEquiv (bar (z ⊗ₜ[ℝ] a)) =
      Kc * (complexMatrixEquiv (z ⊗ₜ[ℝ] a)).conjTranspose * Kc := by
  rw [bar_tmul, complexMatrixEquiv_tmul, splitMatrixEquiv_star,
    map_mul, map_mul, realToComplexMatrix_transpose, complexMatrixEquiv_tmul,
    Matrix.conjTranspose_smul]
  simp only [Kc, smul_mul_assoc, mul_smul_comm]

/-- The preserved complex Clifford conjugation is the actual matrix form adjoint. -/
theorem complexMatrixEquiv_bar (x : CCl) :
    complexMatrixEquiv (bar x) = Kc * (complexMatrixEquiv x).conjTranspose * Kc := by
  induction x using TensorProduct.inductionOn with
  | tmul z a => exact complexMatrixEquiv_bar_tmul z a
  | add x y hx hy =>
    simp only [bar_add, map_add, Matrix.conjTranspose_add, mul_add, add_mul, hx, hy]

/-- The bridge also covers the inverse image of every complex matrix. -/
theorem complexMatrixEquiv_bar_inverse (A : CMatrix) :
    complexMatrixEquiv (bar (complexMatrixEquiv.symm A)) = Kc * A.conjTranspose * Kc := by
  rw [complexMatrixEquiv_bar, complexMatrixEquiv.apply_symm_apply]

theorem complexMatrixEquiv_symm_adjoint (A : CMatrix) :
    complexMatrixEquiv.symm (Kc * A.conjTranspose * Kc) =
      bar (complexMatrixEquiv.symm A) := by
  apply complexMatrixEquiv.injective
  rw [complexMatrixEquiv.apply_symm_apply, complexMatrixEquiv_bar_inverse]

/-- This equivalence uses the actual complex representation and bar, with no extra premise. -/
theorem skew_iff_matrix (x : CCl) :
    Skew x ↔ Kc * (complexMatrixEquiv x).conjTranspose * Kc = -complexMatrixEquiv x := by
  unfold Skew
  rw [← complexMatrixEquiv_bar, ← map_neg, complexMatrixEquiv.injective.eq_iff]

end HyperbolicSpinor
