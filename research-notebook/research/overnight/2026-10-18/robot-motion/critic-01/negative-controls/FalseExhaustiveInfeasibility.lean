import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : checkTimedCandidate (1/5) (1/2) (15/2) (13/25) (17/10) [(11/50,1/50)] (-1/50) (31/50) = false := by
  rw [omitted_feasible_candidate]
  norm_num
