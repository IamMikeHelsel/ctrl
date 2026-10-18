import ComplexControls
import Lean.Util.CollectAxioms
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex
namespace IndependentComplexReview

theorem arbitrary_matrix_inverse (A : CMatrix) :
    ∃! x : CCl, complexMatrixEquiv x = A := by
  refine ⟨complexMatrixEquiv.symm A, complexMatrixEquiv.apply_symm_apply A, ?_⟩
  intro x hx
  apply complexMatrixEquiv.injective
  simpa only [complexMatrixEquiv.apply_symm_apply] using hx

theorem tensor_round_trip (x : CCl) : complexMatrixEquiv.symm (complexMatrixEquiv x) = x :=
  complexMatrixEquiv.symm_apply_apply x

theorem inverse_preserves_genuine_product (A B : CMatrix) :
    complexMatrixEquiv.symm (A*B) = complexMatrixEquiv.symm A * complexMatrixEquiv.symm B :=
  map_mul _ A B

theorem product_coordinate (x y : CCl) (I T : Finset J) :
    complexMatrixEquiv (x*y) I T = ∑ U, complexMatrixEquiv x I U * complexMatrixEquiv y U T := by
  rw [map_mul]
  rfl

theorem pure_scalar_unconjugated (z : ℂ) :
    complexMatrixEquiv (z ⊗ₜ[ℝ] (1 : Cl)) = z • (1 : CMatrix) := by simp

theorem mixed_coordinate (z w : ℂ) (a b : Cl) (I T : Finset J) :
    complexMatrixEquiv ((z ⊗ₜ[ℝ] a)+(w ⊗ₜ[ℝ] b)) I T =
      z*(splitMatrixEquiv a I T : ℂ)+w*(splitMatrixEquiv b I T : ℂ) := by
  rw [map_add]
  change complexMatrixEquiv (z ⊗ₜ[ℝ] a) I T + complexMatrixEquiv (w ⊗ₜ[ℝ] b) I T = _
  rw [complexMatrixEquiv_tmul_entry, complexMatrixEquiv_tmul_entry]

theorem adjoint_scalar_on_arbitrary_inverse (z : ℂ) (A : CMatrix) :
    complexMatrixEquiv (bar (z • complexMatrixEquiv.symm A)) =
      star z • (Kc * A.conjTranspose * Kc) := by
  rw [bar_smul, map_smul, complexMatrixEquiv_bar_inverse]

theorem mixed_adjoint (z w : ℂ) (a b : Cl) :
    complexMatrixEquiv (bar ((z ⊗ₜ[ℝ] a)+(w ⊗ₜ[ℝ] b))) =
      star z • realToComplexMatrix (splitMatrixEquiv (star a)) +
      star w • realToComplexMatrix (splitMatrixEquiv (star b)) := by
  rw [bar_add, map_add, bar_tmul, bar_tmul, complexMatrixEquiv_tmul, complexMatrixEquiv_tmul]

theorem adjoint_product_of_arbitrary_matrices (A B : CMatrix) :
    complexMatrixEquiv (bar (complexMatrixEquiv.symm (A*B))) =
      (Kc * B.conjTranspose * Kc) * (Kc * A.conjTranspose * Kc) := by
  rw [map_mul, bar_mul, map_mul, complexMatrixEquiv_bar_inverse, complexMatrixEquiv_bar_inverse]

theorem actual_form_identity :
    Kc = realToComplexMatrix (negativeMatrix 0 * negativeMatrix 1 * negativeMatrix 2 *
      negativeMatrix 3 * negativeMatrix 4 * negativeMatrix 5 * negativeMatrix 6) := rfl

theorem involution_on_every_matrix (A : CMatrix) :
    Kc * (Kc*A.conjTranspose*Kc).conjTranspose*Kc = A := by
  rw [← complexMatrixEquiv_bar_inverse]
  rw [← complexMatrixEquiv_bar, complexMatrixEquiv_symm_adjoint]
  rw [bar_involutive, complexMatrixEquiv.apply_symm_apply]

theorem imaginary_identity_not_fixed :
    complexMatrixEquiv (bar (Complex.I ⊗ₜ[ℝ] (1 : Cl))) ≠
      complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) := by
  rw [bar_tmul]
  simp only [star_one, complexMatrixEquiv_tmul, map_one]
  intro h
  have hh := congrFun (congrFun h (∅ : Finset J)) ∅
  norm_num [Matrix.one_apply, Complex.ext_iff] at hh

theorem faithful_nonzero : complexMatrixEquiv (1 : CCl) ≠ 0 := by simp

def E01 : CMatrix := Matrix.single ∅ {0} 1
def E10 : CMatrix := Matrix.single {0} ∅ 1

theorem matrix_multiplication_is_not_pointwise :
    (E01 * E10) ∅ ∅ = 1 ∧ E01 ∅ ∅ * E10 ∅ ∅ = 0 := by
  simp [E01, E10]

theorem two_actual_preimages_noncommute :
    complexMatrixEquiv.symm E01 * complexMatrixEquiv.symm E10 ≠
      complexMatrixEquiv.symm E10 * complexMatrixEquiv.symm E01 := by
  intro h
  have hh := congrArg (fun x => complexMatrixEquiv x ∅ ∅) h
  simp [map_mul, E01, E10] at hh

theorem skew_condition_roundtrip (A : CMatrix) :
    Skew (complexMatrixEquiv.symm A) ↔ Kc*A.conjTranspose*Kc = -A := by
  rw [skew_iff_matrix, complexMatrixEquiv.apply_symm_apply]

theorem imaginary_is_skew : Skew (Complex.I • (1 : CCl)) := by
  unfold Skew
  rw [bar_I_smul]
  simp [bar]

theorem identity_not_skew : ¬ Skew (1 : CCl) := by
  intro h
  have hh := congrArg (fun x => complexMatrixEquiv x ∅ ∅) h
  norm_num [bar, Matrix.one_apply] at hh

end IndependentComplexReview
