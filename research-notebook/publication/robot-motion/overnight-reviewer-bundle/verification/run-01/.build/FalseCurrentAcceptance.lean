import SuccessorGuard
open RobotMotion.AccelerationAdmission.SuccessorCheck
example : checkSuccessor 1 (1/10) (7/2) [(0,1)] = true := by
  rw [current_time_rejected]
  norm_num
