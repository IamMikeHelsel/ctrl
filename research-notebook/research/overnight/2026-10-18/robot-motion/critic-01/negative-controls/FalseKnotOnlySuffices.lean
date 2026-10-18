import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : qAcceleration 1 [(0,1)] (4/3) ≤ 1/2 := by
  rw [off_knot_peak]
  norm_num
