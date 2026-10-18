import ReviewWitnesses
open RobotMotion RobotMotion.HistoryPruning RobotMotion.AccelerationAdmission IndependentPruningReview
example : qRetained 1 4 [(0,1)] = [(0,1)] := by
  rw [end_boundary_prunes]
  norm_num
