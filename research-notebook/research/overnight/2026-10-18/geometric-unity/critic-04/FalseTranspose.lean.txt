import ReviewClient
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex IndependentComplexReview
example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = Kc*(complexMatrixEquiv (Complex.I • (1 : CCl))).transpose*Kc := by
 rw [complexMatrixEquiv_bar_I, complexMatrixEquiv_I, Matrix.transpose_smul, Matrix.transpose_one, mul_smul_comm, mul_one, smul_mul_assoc, Kc_square]
