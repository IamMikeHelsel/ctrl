import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : commitOK pendingReturn {changedBase with version := movingBase.version} returnTask onTime = true := by
  rw [rejects_reused_history_version]
  norm_num
