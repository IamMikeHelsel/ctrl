import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : position 0 (1/5) (realEvents (commit pendingReturn movingBase returnTask tooLate).events) (17/10) = 0 := by
  rw [late_rejection_retains_old]
  norm_num [movingBase,realEvents,realEvent,position,response,F0,P]
