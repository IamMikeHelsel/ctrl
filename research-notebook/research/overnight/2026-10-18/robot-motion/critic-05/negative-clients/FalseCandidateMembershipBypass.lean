import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : certificateOK missingCandidate = true := by
  rw [omitted_selected_candidate_rejected]
  norm_num
