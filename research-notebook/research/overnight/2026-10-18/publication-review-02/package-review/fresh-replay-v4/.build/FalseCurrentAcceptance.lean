import VelocityFixtures
open RobotMotion.VelocityAdmission
example : checkVelocity 1 0 (7/2) [(0,1)] = true := by
  rw [current_inside_tail_rejected]
  norm_num
