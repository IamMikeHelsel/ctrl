import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview02
example : position 0 (1/5) (realEvents deferredReturn) (1/2) = 0 := by
  rw [delayed_reference_progress]
  norm_num
