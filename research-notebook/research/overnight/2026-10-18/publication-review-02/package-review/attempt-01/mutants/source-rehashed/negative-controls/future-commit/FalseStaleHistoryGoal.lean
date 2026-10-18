import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : position 0 (1/5) (realEvents (appendPending pendingReturn changedBase).events) (17/10) = (returnTask.goal:ℝ) := by
  rw [stale_base_real_deadline_failure.1]
  norm_num [returnTask]
