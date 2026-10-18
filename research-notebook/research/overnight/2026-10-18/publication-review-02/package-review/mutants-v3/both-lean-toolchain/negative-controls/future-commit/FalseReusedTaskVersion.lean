import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : commitOK pendingReturn movingBase {changedTask with version := returnTask.version} onTime = true := by
  rw [rejects_reused_task_version]
  norm_num
