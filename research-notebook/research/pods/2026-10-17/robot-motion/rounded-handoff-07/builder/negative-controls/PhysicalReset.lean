import HandoffWitnesses
open LeanControls LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.HandoffWitnesses
example : |coordinates 0 (scaledError 10 unitPosition rest 0) 0| ≤ (0:ℝ) := by
  norm_num [unitPosition,rest,scaledError,error,coordinates,scaleState]
