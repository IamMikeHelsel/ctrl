import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck IndependentSuccessorReview
example : checkSuccessor 0 1 0 [] = true := by
  rw [zero_width_rejected]
  norm_num
