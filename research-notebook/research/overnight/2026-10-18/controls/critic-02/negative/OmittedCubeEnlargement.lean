import ConstantBias
open LeanControls.UncertainLag LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.ConstantBias
example : |coordinates (offset 10 (1/100)) (scaleState 10 (![-(1/5000),0,0] : State)) 0| ≤ (1/5000:ℝ) := by
  norm_num [coordinates,scaleState,offset]
