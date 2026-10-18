import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck IndependentSuccessorReview
example : checkSuccessor 1 0 0 [(0,100),(0,-100)] = false := by
  rw [repeated_cancel]
  norm_num
