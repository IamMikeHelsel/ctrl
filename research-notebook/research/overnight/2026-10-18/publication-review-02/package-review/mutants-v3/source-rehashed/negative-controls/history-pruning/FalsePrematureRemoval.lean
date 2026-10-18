import HistoryPruning
open RobotMotion.HistoryPruning
example : qRetained 1 1 [(0,1)] = [] := by
  rw [premature_event_retained]
  norm_num
