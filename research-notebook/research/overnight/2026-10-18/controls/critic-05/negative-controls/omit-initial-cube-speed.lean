import ReviewClients
open Set LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.Settling
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness ControlsReview05
noncomputable section
example : |largeInitial 2 1| ≤ 1/1000 := by
  norm_num [largeInitial]
