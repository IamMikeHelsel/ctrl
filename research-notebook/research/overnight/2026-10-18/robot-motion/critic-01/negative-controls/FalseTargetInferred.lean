import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : position 0 1 (realEvents [(0,1)]) 4 = 0 := by
  rw [accepted_target_is_sum]
  norm_num
