import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : position 0 (1/5) (realEvents (appendPending pendingReturn (commit pendingReturn movingBase returnTask onTime)).events) (17/10) = 0 := by
  rw [reachable_duplicate_real_failure]
  norm_num
