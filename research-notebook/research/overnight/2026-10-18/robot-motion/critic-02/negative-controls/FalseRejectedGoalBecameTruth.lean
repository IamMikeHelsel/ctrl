import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview02
example : position 0 (1/5) (realEvents [(11/50,1/50)]) (17/10) = 0 := by
  rw [retained_request_after_rejection]
  norm_num
