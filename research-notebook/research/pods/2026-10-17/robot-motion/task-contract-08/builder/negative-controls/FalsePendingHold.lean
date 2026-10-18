import TaskFixtures
open RobotMotion RobotMotion.TaskContract
example : position 0 (1/5) [(1,1/50)] (9/5) = 0 := by
  norm_num [position,response,F0,P]
