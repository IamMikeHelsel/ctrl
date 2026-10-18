import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : ¬ ((1/2:ℝ) < |velocity 1 [(0,1),(1,-1)] (9/5)|) := by
  rw [iff_true_intro interior_real_violation]
  norm_num
