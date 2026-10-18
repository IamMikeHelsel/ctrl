import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : checkVelocity 1 (1/6) 0 [(0,1),(1/4,-1)] = true := by
  rw [conservative_rejection]
  norm_num
