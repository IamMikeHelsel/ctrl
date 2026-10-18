import Client
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex
example (a b : CCl) : complexMatrixEquiv (bar (a*b)) = complexMatrixEquiv (bar a) * complexMatrixEquiv (bar b) := by
  rw [bar_mul, map_mul]
