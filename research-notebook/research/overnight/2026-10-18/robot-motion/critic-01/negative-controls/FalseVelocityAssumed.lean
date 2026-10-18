import Witnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview
example : velocity 1 (realEvents [(0,1)]) 2 ≤ 1/2 := by
  rw [admitted_reference_can_exceed_arbitrary_velocity_limit]
  norm_num
