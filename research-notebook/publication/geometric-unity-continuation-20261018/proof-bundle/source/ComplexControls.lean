import ComplexBridge
import AdjointControls

noncomputable section
open scoped TensorProduct
namespace HyperbolicSpinor
open GUClifford GUComplex

@[simp] theorem complexMatrixEquiv_embed (a : Cl) :
    complexMatrixEquiv (embed a) = realToComplexMatrix (splitMatrixEquiv a) := by
  change complexMatrixEquiv ((1 : ℂ) ⊗ₜ[ℝ] a) = _
  simp

@[simp] theorem complexMatrixEquiv_I :
    complexMatrixEquiv (Complex.I • (1 : CCl)) = Complex.I • (1 : CMatrix) := by
  simp

theorem complexMatrixEquiv_bar_I :
    complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = -Complex.I • (1 : CMatrix) := by
  rw [bar_I_smul]
  simp [bar]

/-- Omitting complex conjugation is false even on the imaginary scalar identity. -/
theorem plain_transpose_not_bar :
    complexMatrixEquiv (bar (Complex.I • (1 : CCl))) ≠
      Kc * (complexMatrixEquiv (Complex.I • (1 : CCl))).transpose * Kc := by
  rw [complexMatrixEquiv_bar_I, complexMatrixEquiv_I, Matrix.transpose_smul,
    Matrix.transpose_one, mul_smul_comm, mul_one, smul_mul_assoc, Kc_square]
  intro h
  have he := congrFun (congrFun h ∅) ∅
  norm_num [Matrix.one_apply, Complex.ext_iff] at he

/-- Plain transpose also fails when evaluated through the actual equivalence. -/
theorem imaginary_not_fixed :
    complexMatrixEquiv (bar (Complex.I • (1 : CCl))) ≠
      complexMatrixEquiv (Complex.I • (1 : CCl)) := by
  rw [complexMatrixEquiv_bar_I, complexMatrixEquiv_I]
  intro h
  have he := congrFun (congrFun h ∅) ∅
  norm_num [Matrix.one_apply, Complex.ext_iff] at he

/-- Every complex matrix, including off-diagonal ones, has an actual Clifford preimage. -/
theorem arbitrary_matrix_preimage (A : CMatrix) :
    ∃ x : CCl, complexMatrixEquiv x = A := complexMatrixEquiv.surjective A

/-- Matrix multiplication sums over the common index. -/
theorem off_diagonal_product :
    (Matrix.single (∅ : Finset J) {0} (1 : ℂ) *
      Matrix.single ({0} : Finset J) ∅ (1 : ℂ) : CMatrix) = Matrix.single ∅ ∅ 1 := by
  simp

theorem off_diagonal_noncommute :
    (Matrix.single (∅ : Finset J) {0} (1 : ℂ) *
      Matrix.single ({0} : Finset J) ∅ (1 : ℂ) : CMatrix) ≠
    Matrix.single ({0} : Finset J) ∅ (1 : ℂ) * Matrix.single ∅ {0} 1 := by
  intro h
  have he := congrFun (congrFun h ∅) ∅
  simp at he

/-- The noncommuting test is transported back to the actual tensor algebra. -/
theorem preimages_noncommute :
    let a := complexMatrixEquiv.symm (Matrix.single (∅ : Finset J) {0} (1 : ℂ))
    let b := complexMatrixEquiv.symm (Matrix.single ({0} : Finset J) ∅ (1 : ℂ))
    a * b ≠ b * a := by
  dsimp
  intro h
  apply off_diagonal_noncommute
  simpa only [map_mul, complexMatrixEquiv.apply_symm_apply] using congrArg complexMatrixEquiv h

/-- A mixed real and imaginary input still reverses product order under bar. -/
theorem mixed_product_bar (z w : ℂ) (a b : Cl) :
    complexMatrixEquiv (bar ((z ⊗ₜ[ℝ] a) * (w ⊗ₜ[ℝ] b))) =
      complexMatrixEquiv (bar (w ⊗ₜ[ℝ] b)) * complexMatrixEquiv (bar (z ⊗ₜ[ℝ] a)) := by
  rw [bar_mul, map_mul]

end HyperbolicSpinor
