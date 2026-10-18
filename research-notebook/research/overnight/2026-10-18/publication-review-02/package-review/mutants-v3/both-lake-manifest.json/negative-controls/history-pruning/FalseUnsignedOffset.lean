import HistoryPruning
open RobotMotion.HistoryPruning
example : qCompletedOffset 1 4 [(0,2),(0,-3),(1,4),(10,5)] = 5 := by
  rw [signed_repeated_offset]
  norm_num
