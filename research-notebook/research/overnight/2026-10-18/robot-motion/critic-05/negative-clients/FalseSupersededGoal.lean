import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : position 0 (1/5) (realEvents (appendPending pendingReturn movingBase).events) (17/10) = (changedTask.goal:ℝ) := by
  rw [stale_task_real_deadline_failure.1]
  norm_num [changedTask,returnTask]
