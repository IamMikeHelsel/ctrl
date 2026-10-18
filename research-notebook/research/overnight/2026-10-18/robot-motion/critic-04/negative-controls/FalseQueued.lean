import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : checkVelocity 1 (1/2) 0 [(10,1)] = true := by
  rw [queued_history_rejected]
  norm_num
