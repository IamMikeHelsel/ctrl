import ReviewWitnesses
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview
example : position 0 0 [(0,1)] 0 = position 1 0 [] 0 := by
  rw [zero_width_jet_equality_fails.1,zero_width_jet_equality_fails.2]
  norm_num
