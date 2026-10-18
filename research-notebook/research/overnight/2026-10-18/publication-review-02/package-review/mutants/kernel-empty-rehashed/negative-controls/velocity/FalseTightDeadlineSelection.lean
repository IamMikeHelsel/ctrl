import VelocityFixtures
open RobotMotion.VelocityAdmission
example : chooseVelocityExecution (1/5) (1/15) (1/2) (15/2) (13/25) (13/10)
      [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by
  rw [tight_deadline_no_candidate]
  norm_num
