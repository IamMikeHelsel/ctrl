import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : commitOK pendingReturn movingBase returnTask tooLate = true := by
  rw [rejects_late]
  norm_num
