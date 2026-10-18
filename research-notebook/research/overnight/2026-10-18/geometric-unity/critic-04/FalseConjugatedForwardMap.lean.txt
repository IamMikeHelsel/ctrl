import ReviewClient
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex IndependentComplexReview
example : complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) = -Complex.I • (1 : CMatrix) := by
 rw [pure_scalar_unconjugated]
