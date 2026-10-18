import ComplexControls
import OrderControls
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex
namespace GUComplexClient

theorem pure_entry (z : ℂ) (a : Cl) (I T : Finset J) :
    complexMatrixEquiv (z ⊗ₜ[ℝ] a) I T = z * (splitMatrixEquiv a I T : ℂ) :=
  complexMatrixEquiv_tmul_entry z a I T

theorem nonzero_image : complexMatrixEquiv (1 : CCl) ≠ 0 := by simp

theorem inverse_any_matrix (A : CMatrix) : complexMatrixEquiv (complexMatrixEquiv.symm A) = A :=
  complexMatrixEquiv.apply_symm_apply A

theorem roundtrip_tensor (a : CCl) : complexMatrixEquiv.symm (complexMatrixEquiv a) = a :=
  complexMatrixEquiv.symm_apply_apply a

theorem full_bridge (a : CCl) :
    complexMatrixEquiv (bar a) = Kc * (complexMatrixEquiv a).conjTranspose * Kc :=
  complexMatrixEquiv_bar a

theorem full_inverse_bridge (A : CMatrix) :
    complexMatrixEquiv (bar (complexMatrixEquiv.symm A)) = Kc * A.conjTranspose * Kc :=
  complexMatrixEquiv_bar_inverse A

theorem adjoint_conjugates_scalar (z : ℂ) (x : CCl) :
    complexMatrixEquiv (bar (z • x)) = star z • complexMatrixEquiv (bar x) := by
  rw [bar_smul, map_smul]

theorem mixed_sum (z w : ℂ) (a b : Cl) :
    complexMatrixEquiv ((z ⊗ₜ[ℝ] a) + (w ⊗ₜ[ℝ] b)) =
      z • realToComplexMatrix (splitMatrixEquiv a) + w • realToComplexMatrix (splitMatrixEquiv b) := by
  rw [map_add, complexMatrixEquiv_tmul, complexMatrixEquiv_tmul]

theorem matrix_product (a b : CCl) :
    complexMatrixEquiv (a*b) = complexMatrixEquiv a * complexMatrixEquiv b := map_mul _ _ _

theorem reversed_product (a b : CCl) :
    complexMatrixEquiv (bar (a*b)) = complexMatrixEquiv (bar b) * complexMatrixEquiv (bar a) := by
  rw [bar_mul, map_mul]

theorem positive_vector_skew :
    Kc * (complexMatrixEquiv (cgamma 0)).conjTranspose * Kc = -complexMatrixEquiv (cgamma 0) := by
  rw [← complexMatrixEquiv_bar, bar_gamma, map_neg]

theorem real_scalar_stays_real (r : ℝ) :
    complexMatrixEquiv (((r : ℂ) ⊗ₜ[ℝ] (1 : Cl))) = (r : ℂ) • (1 : CMatrix) := by simp

theorem negative_K_same_complex_adjoint (A : CMatrix) :
    (-Kc) * A.conjTranspose * (-Kc) = Kc * A.conjTranspose * Kc := by
  simp only [neg_mul, mul_neg, neg_neg]

theorem form_involution (A : CMatrix) :
    Kc * (Kc * A.conjTranspose * Kc).conjTranspose * Kc = A := by
  obtain ⟨x, rfl⟩ := complexMatrixEquiv.surjective A
  rw [← complexMatrixEquiv_bar, ← complexMatrixEquiv_bar, bar_involutive]

end GUComplexClient
