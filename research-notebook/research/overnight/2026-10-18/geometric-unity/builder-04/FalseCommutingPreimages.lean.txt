import Client
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex
example : let a := complexMatrixEquiv.symm (Matrix.single (∅ : Finset J) {0} (1 : ℂ)); let b := complexMatrixEquiv.symm (Matrix.single ({0} : Finset J) ∅ (1 : ℂ)); a*b = b*a := by
  dsimp
  apply complexMatrixEquiv.injective
  simp only [map_mul, complexMatrixEquiv.apply_symm_apply]
