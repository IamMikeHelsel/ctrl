import ReviewIntegrationWitnesses
import ReviewTaskWitnesses
open RobotMotion RobotMotion.TaskContract
noncomputable section
example : CompleteBy (1/5) 0 [(1,1/50)] := by norm_num [CompleteBy]
