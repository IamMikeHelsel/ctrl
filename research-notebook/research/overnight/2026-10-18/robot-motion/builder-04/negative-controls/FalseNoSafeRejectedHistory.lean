import VelocityFixtures
open RobotMotion.VelocityAdmission
example : ¬ (∀ t : ℝ, 0 ≤ t → |RobotMotion.velocity 1 [(0,1),(1/4,-1)] t| ≤ 1/6) := by
  have good := rejected_history_is_safe
  simp only [good,not_true_eq_false]
  norm_num
