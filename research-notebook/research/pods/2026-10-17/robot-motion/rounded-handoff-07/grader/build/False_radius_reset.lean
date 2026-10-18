import ReviewWitnesses
open IndependentRoundedReview LeanControls.RobustHold LeanControls.ScaledTracking
example : |coordinates 0 (scaledError 10 negativeUnitPath unitPath 0) 0| ≤ (1:ℝ) := by
  norm_num [coordinates, scaledError, scaleState, LeanControls.TrackingReplan.error, negativeUnitPath, unitPath]
