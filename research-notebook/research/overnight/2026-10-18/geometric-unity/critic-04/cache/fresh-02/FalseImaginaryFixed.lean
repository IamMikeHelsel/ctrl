import ReviewClient
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex IndependentComplexReview
example : complexMatrixEquiv (bar (Complex.I ⊗ₜ[ℝ] (1 : Cl))) = complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) := by
 rw [bar_tmul]
 simp only [star_one, complexMatrixEquiv_tmul, map_one]
