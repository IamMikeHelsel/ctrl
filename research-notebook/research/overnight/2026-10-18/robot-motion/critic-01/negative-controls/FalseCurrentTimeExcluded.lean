import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : checkAcceleration 1 (1/10) (7/2) [(0,1)] = true := by
  rw [current_time_rejects]
  norm_num
