import ReviewerClient
noncomputable section
open Matrix HyperbolicSpinor GUComplex GUClifford
example : complexMatrixEquiv (bar (Complex.I • (1 : CCl))) ∅ ∅ = Complex.I := by
  rw [complexMatrixEquiv_bar_I]
  norm_num [Matrix.one_apply, Complex.ext_iff]
