import ReviewClients
open RobotMotion RobotMotion.FutureCommit MotionReview
example : position 0 (1/5) (realEvents (appendPending noDelta movingBase).events) (17/10) = (returnTask.goal:ℝ) := by
  rw [no_delta_real_goal_failure.1]
  norm_num [returnTask]
