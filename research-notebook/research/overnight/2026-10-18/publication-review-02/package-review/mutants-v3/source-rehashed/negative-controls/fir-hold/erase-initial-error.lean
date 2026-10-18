import FIRHoldWitness
open LeanControls.RobustHold LeanControls.ScaledTracking
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness
example : coordinates 0 (scaledError 10 (biasedReference (1/100))
    (referenceState 0 (1/5) (realEvents deferredReturn)) 0) 0 = 0 := by
  rw [initial_error_not_erased]
  norm_num
