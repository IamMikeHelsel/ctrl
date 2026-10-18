import ReviewWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.AccelerationAdmission.SuccessorCheck IndependentSuccessorReview
example : qJerk 1 [(0,1)] 1 ≤ (1/10:ℚ) := by
  have h := acceleration_acceptance_does_not_imply_small_jerk.2
  have hv : qJerk 1 [(0,1)] 1 = 1 := by decide +kernel
  rw [hv]
  norm_num
