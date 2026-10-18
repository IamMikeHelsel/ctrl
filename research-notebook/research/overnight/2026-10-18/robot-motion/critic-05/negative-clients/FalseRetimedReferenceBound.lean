import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : |acceleration (1/5) (realEvents (appendPending movedExecution movingBase).events) (77/100)| ≤ 1/2 := by
  rw [moved_execution_real_failure.1]
  norm_num
