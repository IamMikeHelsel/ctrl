import TimedAdmission
open RobotMotion RobotMotion.AccelerationAdmission
example : checkTimedCandidate (1/5) (1/2) (15/2) (7/10) (17/10)
    [(11/50,1/50)] (-1/50) (31/50) = true := by
  rw [past_candidate_rejected]
  norm_num
