import RealAdjoint
import Mathlib.Basic.Complex.Basic

noncomputable section
namespace HyperbolicSpinor
open GUClifford

theorem positive_zero_square : positiveMatrix 0 * positiveMatrix 0 = 1 := positive_square

theorem real_matrix_eq_neg_self_zero (A : SpinMatrix) (h : A = -A) : A = 0 := by
  ext I T
  have hv := congrFun (congrFun h I) T
  change A I T = -(A I T) at hv
  change A I T = 0
  linarith

theorem positive_zero_nonzero : positiveMatrix 0 ≠ 0 := positive_not_zero

/-- The Euclidean adjoint does not make a positive Clifford vector skew. -/
theorem positive_not_euclidean_skew : (positiveMatrix 0).transpose ≠ -positiveMatrix 0 := by
  rw [positive_transpose]
  intro h
  exact positive_zero_nonzero (real_matrix_eq_neg_self_zero _ h)

theorem K_ne_one : K ≠ 1 := by
  intro h
  have hc := K_anticommutes_positive 0
  rw [h, mul_one, one_mul] at hc
  exact positive_zero_nonzero (real_matrix_eq_neg_self_zero _ hc)

theorem K_ne_neg_one : K ≠ -1 := by
  intro h
  have hc := K_anticommutes_positive 0
  rw [h, mul_neg, neg_mul, mul_one, one_mul, neg_neg] at hc
  exact positive_zero_nonzero (real_matrix_eq_neg_self_zero _ hc.symm)

/-- Dropping the right K fails even on the first positive vector. -/
theorem omitted_right_K_fails : K * (positiveMatrix 0).transpose ≠ -positiveMatrix 0 := by
  rw [positive_transpose]
  intro h
  apply K_ne_neg_one
  calc
    K = K * (positiveMatrix 0 * positiveMatrix 0) := by rw [positive_zero_square, mul_one]
    _ = (K * positiveMatrix 0) * positiveMatrix 0 := (mul_assoc _ _ _).symm
    _ = (-positiveMatrix 0) * positiveMatrix 0 := by rw [h]
    _ = -1 := by rw [neg_mul, positive_zero_square]

/-- Changing the negative generator to creation plus contraction changes its square. -/
theorem wrong_negative_fock_square :
    (creationMatrix 0 + contractionMatrix 0) * (creationMatrix 0 + contractionMatrix 0) ≠ -1 := by
  have hp : creationMatrix 0 + contractionMatrix 0 = positiveMatrix 0 := by
    rw [positiveMatrix_fock, add_comm]
  rw [hp, positive_zero_square]
  intro h
  have he := congrFun (congrFun h ∅) ∅
  norm_num at he

/-- A global sign of K cancels from its adjoint; it is not a failed bridge. -/
theorem negative_K_same_adjoint (A : SpinMatrix) :
    (-K) * A.transpose * (-K) = K * A.transpose * K := by
  simp only [neg_mul, mul_neg, neg_neg]

/-- Reversing seven anticommuting factors changes only the global sign. -/
theorem reversed_negative_product :
    negativeMatrix 6 * negativeMatrix 5 * negativeMatrix 4 * negativeMatrix 3 *
      negativeMatrix 2 * negativeMatrix 1 * negativeMatrix 0 = -K := by
  have h := congrArg Neg.neg K_transpose
  simpa only [K, Matrix.transpose_mul, negative_transpose, neg_mul, mul_neg,
    neg_neg, mul_assoc] using h

abbrev ComplexSpinMatrix := Matrix (Finset J) (Finset J) ℂ

/-- A concrete scalar control, not a complex representation theorem. -/
theorem imaginary_scalar_plain_transpose_fails :
    ((Complex.I : ℂ) • (1 : ComplexSpinMatrix)).transpose ≠
      -(Complex.I • (1 : ComplexSpinMatrix)) := by
  intro h
  have he := congrFun (congrFun h ∅) ∅
  norm_num [Matrix.transpose_apply, Matrix.one_apply, Complex.ext_iff] at he

end HyperbolicSpinor
