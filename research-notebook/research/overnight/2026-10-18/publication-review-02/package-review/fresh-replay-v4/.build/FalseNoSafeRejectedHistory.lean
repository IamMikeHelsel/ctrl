import VelocityFixtures
open RobotMotion.VelocityAdmission
example : ¬ (∀ t : ℝ, 0 ≤ t → |RobotMotion.velocity 1 [(0,1),(1/4,-1)] t| ≤ 1/6) := by
  rw [iff_true_intro rejected_history_is_safe]
  norm_num
