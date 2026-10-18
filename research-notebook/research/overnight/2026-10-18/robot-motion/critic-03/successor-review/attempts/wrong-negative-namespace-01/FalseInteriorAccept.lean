import ReviewWitnesses
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview
example : checkSuccessor 1 (1/2) 0 [(0,1)] = true := by
  rw [interior_peak_rejected]
  norm_num
