import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : qAcceleration 1 [(0,1),(1,2),(2,3)] (5/2) = 0 := by
  rw [plateau_nonzero]
  norm_num
