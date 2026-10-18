import ReviewIntegrationWitnesses
import ReviewTaskWitnesses
open RobotMotion RobotMotion.TaskContract
noncomputable section
example (accepted : check (1/5) (15/2) 0 [(11/50,1/50),(13/25,-1/50)] = true) : |acceleration (1/5) [(11/50,1/50),(13/25,-1/50)] (77/100)| ≤ 1/2 := by norm_num [acceleration,response,F2,P]
