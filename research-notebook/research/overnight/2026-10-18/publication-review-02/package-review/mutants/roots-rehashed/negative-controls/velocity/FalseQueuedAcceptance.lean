import VelocityFixtures
open RobotMotion.VelocityAdmission
example : checkVelocity 1 (1/2) 0 [(10,1)] = true := by
  rw [queued_history_rejected]
  norm_num
