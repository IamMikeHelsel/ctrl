import VelocityFixtures
open RobotMotion.VelocityAdmission
example : checkVelocity 1 (1/6) 0 [(0,1),(1/4,-1)] = true := by
  rw [conservative_rejection]
  norm_num
