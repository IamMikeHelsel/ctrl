import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : commitOK pendingReturn movingBase returnTask delayedCommit = true := by
  rw [rejects_delayed_commit]
  norm_num
