import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview02
example : shifted (1/80000) (17/10) 0 = 0 := by
  rw [actual_position_need_not_equal_target]
  norm_num
