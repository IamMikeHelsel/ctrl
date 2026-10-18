import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : SuccessorCheck.qNext [1,1,0,2,2,3] 1 = some 1 := by
  rw [strict_successor_duplicates]
  norm_num
