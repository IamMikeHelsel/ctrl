import HistoryPruning
open RobotMotion RobotMotion.HistoryPruning
example : position 0 1 [(0,1)] 4 = 0 := by
  rw [completed_nonzero_position]
  norm_num
