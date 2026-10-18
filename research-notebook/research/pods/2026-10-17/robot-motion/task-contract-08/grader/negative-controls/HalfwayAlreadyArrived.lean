import ReviewIntegrationWitnesses
import ReviewTaskWitnesses
open RobotMotion RobotMotion.TaskContract
noncomputable section
example : |position 0 (1/5) [(11/50,1/50)] (31/50) - (1/50:ℝ)| ≤ 1/5000 := by norm_num [position,response,F0,P]
