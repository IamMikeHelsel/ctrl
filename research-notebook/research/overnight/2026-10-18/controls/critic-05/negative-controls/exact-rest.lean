import ReviewClients
open Set LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.Settling
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness ControlsReview05
noncomputable section
example : residualMotion (171/50) 1 = 0 := by
  have h := residual_terminal_speed_nonzero
  simp_all
