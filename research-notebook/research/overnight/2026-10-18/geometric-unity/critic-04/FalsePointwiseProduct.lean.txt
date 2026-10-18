import ReviewClient
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex IndependentComplexReview
example : (E01*E10) (∅ : Finset J) ∅ = E01 ∅ ∅ * E10 ∅ ∅ := by
 simp only [E01, E10, Matrix.single_mul_single_same]
