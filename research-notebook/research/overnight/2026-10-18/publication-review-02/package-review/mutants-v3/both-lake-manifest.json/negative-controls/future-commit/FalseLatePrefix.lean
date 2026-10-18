import FutureCommitFixtures
open RobotMotion RobotMotion.FutureCommit
example : position 0 (1/5) (realEvents (appendPending pendingReturn movingBase).events) (7/10) = position 0 (1/5) (realEvents movingBase.events) (7/10) := by
  norm_num [appendPending,pendingReturn,movingBase,realEvents,realEvent,position,response,F0,P]
