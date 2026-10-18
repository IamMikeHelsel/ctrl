import ReviewWitnesses
open IndependentRoundedReview LeanControls.RobustHold LeanControls.ScaledTracking
example : ∀ i, |coordinates 0 (scaledError 10 unitPath zeroPath 0) i| ≤ 0 := by
  intro i
  fin_cases i <;> norm_num [coordinates, scaledError, scaleState, LeanControls.TrackingReplan.error, zeroPath, unitPath]
