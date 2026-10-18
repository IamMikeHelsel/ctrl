import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : checkTimedCandidate 1 100 100 0 4 [(10,0)] 1 0 = true := by
  rw [future_commitment_rejected]
  norm_num
