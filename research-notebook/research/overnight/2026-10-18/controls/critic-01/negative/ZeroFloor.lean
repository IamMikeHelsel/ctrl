import Settling
open LeanControls.RobustHold LeanControls.UncertainLag
example : transformedRHS 8 1 (![0,0,0] : State) 2 ≤ (0:ℝ) := by
  norm_num [transformedRHS]
