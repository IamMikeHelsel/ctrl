import SplitSpinor
open HyperbolicSpinor GUClifford
example : splitMatrix (gamma 7) * splitMatrix (gamma 7) = 1 := by
  exact negative_square
