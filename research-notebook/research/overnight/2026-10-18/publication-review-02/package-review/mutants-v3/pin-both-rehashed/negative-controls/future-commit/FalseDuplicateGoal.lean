import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : position 0 (1/5) (realEvents (appendPending pendingReturn onceCommitted).events) (17/10) = (returnTask.goal:ℝ) := by
  rw [duplicate_real_deadline_failure.1]
  norm_num [returnTask]
