import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : commitOK tightPending movingBase tightTask onTime = true := by
  rw [tight_commit_rejected]
  norm_num
