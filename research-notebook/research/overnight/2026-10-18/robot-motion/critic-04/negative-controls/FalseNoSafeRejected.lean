import ReviewerWitnesses
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : ¬ (∀ t : ℝ, 0 ≤ t → |velocity 1 [(0,1),(1/4,-1)] t| ≤ 1/6) := by
  rw [iff_true_intro rejected_history_is_safe]
  norm_num
