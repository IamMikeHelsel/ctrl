import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck IndependentSuccessorReview
example : qNext [3,0,1,1,2] 1 = some 1 := by
  rw [exact_successor]
  norm_num
