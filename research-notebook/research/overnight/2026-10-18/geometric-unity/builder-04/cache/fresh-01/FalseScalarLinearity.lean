import Client
noncomputable section
open scoped TensorProduct
open HyperbolicSpinor GUClifford GUComplex
example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) = Complex.I • complexMatrixEquiv (bar (1 : CCl)) := by
  rw [complexMatrixEquiv_bar_I]
  simp only [bar, star_one, map_one]
