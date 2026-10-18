import ReviewClients
open Set LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.Settling
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness ControlsReview05
noncomputable section
example : changingRate 0 = changingRate 2 := by
  norm_num [changingRate]
