import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck IndependentSuccessorReview
example : checkSuccessor 1 (1/10) (7/2) [(0,1)] = true := by
  rw [current_time_rejected]
  norm_num
