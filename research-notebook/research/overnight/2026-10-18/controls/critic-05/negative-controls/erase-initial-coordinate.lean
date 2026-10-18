import ReviewClients
open Set LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.Settling
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness ControlsReview05
noncomputable section
example : coordinates 0 (scaledError 10 residualMotion
      (referenceState 0 (1/5) (realEvents deferredReturn)) 0) 0 = 0 := by
  norm_num [residualMotion,coordinates,scaledError,scaleState,error,referenceState]
