import ReviewClient
noncomputable section
open HyperbolicSpinor GUClifford
example : ((Complex.I : ℂ) • (1 : ComplexSpinMatrix)).transpose = -(Complex.I • (1 : ComplexSpinMatrix)) := by
  ext I J
  simp [Matrix.transpose_apply, Matrix.one_apply]
