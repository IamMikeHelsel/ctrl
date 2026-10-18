import ReviewWitnesses
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview
example : position 0 1 [(0,1)] 1 = 1 := by
  rw [active_motion_partial]
  norm_num
