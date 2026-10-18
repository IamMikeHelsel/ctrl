import ReviewClients
open Set LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.TrackingReplan LeanControls.Settling
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness ControlsReview05
noncomputable section
example : ¬ ¬ IsTrajectory 2 changingRate
      (fun s => holdInput 10 0 (fun u => biasedReference (1/200) (71/50+u)) s +
        changingDisturbance s)
      (fun s => biasedReference (1/200) (71/50+s)) := by
  simp only [not_not,wrong_clock_is_not_trajectory]
