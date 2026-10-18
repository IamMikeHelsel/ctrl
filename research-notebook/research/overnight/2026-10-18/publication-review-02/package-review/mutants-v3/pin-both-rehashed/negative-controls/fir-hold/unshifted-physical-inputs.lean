import FIRHoldWitness
open RobotMotion.FIRHoldWitness
example : wrongClockRHS = 0 := by
  rw [wrong_clock_rhs_nonzero]
  norm_num
