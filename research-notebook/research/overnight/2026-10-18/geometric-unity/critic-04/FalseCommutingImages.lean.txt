import ReviewClient
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex IndependentComplexReview
example : complexMatrixEquiv.symm E01 * complexMatrixEquiv.symm E10 = complexMatrixEquiv.symm E10 * complexMatrixEquiv.symm E01 := by
 apply complexMatrixEquiv.injective
 simp only [map_mul, complexMatrixEquiv.apply_symm_apply]
