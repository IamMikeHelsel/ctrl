import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission IndependentMotionReview02
example : checkAcceleration (1/5) (1/2) 0 returnGenerous = true := by
  rw [new_acceleration_guard_rejects]
  norm_num
