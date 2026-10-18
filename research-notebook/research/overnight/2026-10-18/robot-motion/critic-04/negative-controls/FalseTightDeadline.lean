import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : chooseVelocityExecution (1/5) (1/15) (1/2) (15/2) (13/25) (13/10) [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by
  rw [tight_deadline_no_candidate]
  norm_num
