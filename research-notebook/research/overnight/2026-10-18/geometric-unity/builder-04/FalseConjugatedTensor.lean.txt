import Client
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex
example : complexMatrixEquiv (Complex.I ⊗ₜ[ℝ] (1 : Cl)) = -Complex.I • (1 : CMatrix) := by
  simp only [complexMatrixEquiv_tmul, map_one]
