import FIRHoldWitness
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness
example : position 0 (1/5) (realEvents deferredReturn) (1/2) = 0 := by
  rw [wrong_clock_is_nonzero]
  norm_num
