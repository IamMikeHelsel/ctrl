import Settling
open LeanControls.RobustHold LeanControls.UncertainLag
example : transformedRHS 8 0 (![1,9/10,4/5] : State) 0 ≤ -(1/2:ℝ) := by
  norm_num [transformedRHS]
