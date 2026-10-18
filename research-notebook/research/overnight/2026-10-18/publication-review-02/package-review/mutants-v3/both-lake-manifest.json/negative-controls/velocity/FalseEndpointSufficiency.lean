import VelocityFixtures
open RobotMotion.VelocityAdmission
example : (∀ t : ℝ, 0 ≤ t → |RobotMotion.velocity 1 [(0,1),(1,-1)] t| ≤ 1/2) := by
  intro t ht
  have h := interior_real_violation
  have bad : |RobotMotion.velocity 1 [(0,1),(1,-1)] (9/5)| ≤ 1/2 := by
    norm_num [RobotMotion.velocity,RobotMotion.response,RobotMotion.F1,RobotMotion.P]
  exact False.elim (not_le_of_gt h bad)
