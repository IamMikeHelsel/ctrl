import SuccessorGuard
open RobotMotion.AccelerationAdmission.SuccessorCheck
example : qNext [3,0,1,1,2] 1 = some 3 := by
  rw [unsorted_repeated_successor]
  norm_num
