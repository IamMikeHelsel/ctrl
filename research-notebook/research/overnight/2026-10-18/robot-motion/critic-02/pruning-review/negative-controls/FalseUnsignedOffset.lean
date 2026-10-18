import ReviewWitnesses
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview
example : qCompletedOffset 1 4 [(0,-2),(10,7),(0,3),(1,-4)] = 5 := by
  rw [exact_boundary_signed.2]
  norm_num
