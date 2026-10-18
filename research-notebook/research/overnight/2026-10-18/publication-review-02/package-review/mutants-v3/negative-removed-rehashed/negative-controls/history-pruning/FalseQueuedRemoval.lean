import HistoryPruning
open RobotMotion.HistoryPruning
example : qRetained 1 4 [(10,1)] = [] := by
  rw [queued_event_retained]
  norm_num
