import TimedAdmission
open RobotMotion RobotMotion.AccelerationAdmission
example : chooseExecution (1/5) (1/2) (15/2) (13/25) (13/10)
    [(11/50,1/50)] (-1/50) [13/25,31/50] = some (31/50) := by
  rw [insufficient_candidate_deadline]
  norm_num
