import AdjointControls
import OrderControls
noncomputable section
open HyperbolicSpinor GUClifford
namespace AdjointReview

theorem all_elements (x : Cl) :
    splitMatrixEquiv (star x) = K * (splitMatrixEquiv x).transpose * K :=
  splitMatrixEquiv_star x

theorem every_matrix (A : SpinMatrix) :
    splitMatrixEquiv (star (splitMatrixEquiv.symm A)) = K * A.transpose * K := by
  simpa using splitMatrixEquiv_star (splitMatrixEquiv.symm A)

theorem inverse_bridge (A : SpinMatrix) :
    splitMatrixEquiv.symm (K * A.transpose * K) = star (splitMatrixEquiv.symm A) := by
  apply splitMatrixEquiv.injective
  simp only [AlgEquiv.apply_symm_apply, every_matrix]

theorem vector (v : V) :
    K * (splitMatrixEquiv (CliffordAlgebra.ι Q v)).transpose * K =
      -splitMatrixEquiv (CliffordAlgebra.ι Q v) := realAdjoint_vector v

theorem actual_creation (i : J) :
    (LinearMap.toMatrixAlgEquiv spinBasis (create i)).transpose =
      LinearMap.toMatrixAlgEquiv spinBasis (annihilate i) := creation_transpose i

theorem symmetric_involution : K.transpose = K ∧ K * K = 1 :=
  ⟨K_transpose, K_square⟩

theorem reversed_sign :
    negativeMatrix 6 * negativeMatrix 5 * negativeMatrix 4 * negativeMatrix 3 *
    negativeMatrix 2 * negativeMatrix 1 * negativeMatrix 0 = -K := reversed_negative_product

theorem sign_independent (A : SpinMatrix) :
    (-K) * A.transpose * (-K) = K * A.transpose * K := negative_K_same_adjoint A

theorem anti_product (A B : SpinMatrix) :
    K * (A*B).transpose * K = (K * B.transpose * K) * (K * A.transpose * K) :=
  realAdjoint_mul A B

theorem not_euclidean : (positiveMatrix 0).transpose ≠ -positiveMatrix 0 :=
  positive_not_euclidean_skew

theorem not_one_sided : K * (positiveMatrix 0).transpose ≠ -positiveMatrix 0 :=
  omitted_right_K_fails

theorem K_not_negative_square : K*K ≠ -1 := by
  rw [K_square]
  intro h
  have he := congrFun (congrFun h ∅) ∅
  norm_num at he

theorem reverse_not_original :
    negativeMatrix 6 * negativeMatrix 5 * negativeMatrix 4 * negativeMatrix 3 *
    negativeMatrix 2 * negativeMatrix 1 * negativeMatrix 0 ≠ K := by
  rw [reversed_negative_product]
  intro h
  have hz : K = 0 := real_matrix_eq_neg_self_zero K h.symm
  have hs := K_square
  rw [hz, zero_mul] at hs
  have he := congrFun (congrFun hs ∅) ∅
  norm_num at he

theorem nonzero_vector : splitMatrixEquiv (gamma 0) ≠ 0 := positive_zero_nonzero

theorem complex_scalar_control :
    ((Complex.I : ℂ) • (1 : ComplexSpinMatrix)).transpose ≠
      -(Complex.I • (1 : ComplexSpinMatrix)) := imaginary_scalar_plain_transpose_fails
end AdjointReview
