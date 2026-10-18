import SuccessorGuard
open RobotMotion.AccelerationAdmission.SuccessorCheck
example : checkSuccessor 1 (1/2) 0 [(10,1)] = true := by
  rw [queued_peak_rejected]
  norm_num
