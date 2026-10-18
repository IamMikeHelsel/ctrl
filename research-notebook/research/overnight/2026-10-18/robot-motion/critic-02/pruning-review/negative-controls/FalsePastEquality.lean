import ReviewWitnesses
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview
example : position 1 1 [] 0 = position 0 1 [(0,1)] 0 := by
  rw [pruned_past_offset_one,past_motion_zero]
  norm_num
