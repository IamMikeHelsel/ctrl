import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : checkVelocity 0 100 0 [(0,1)] = true := by
  rw [invalid_width_nonempty]
  norm_num
