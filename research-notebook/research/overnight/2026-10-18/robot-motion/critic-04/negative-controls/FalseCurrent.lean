import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : checkVelocity 1 (1/2) 2 [(0,1)] = true := by
  rw [exact_current_rejection]
  norm_num
