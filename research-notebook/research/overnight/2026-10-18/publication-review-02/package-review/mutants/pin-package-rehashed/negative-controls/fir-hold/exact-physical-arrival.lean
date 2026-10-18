import FIRHoldWitness
open RobotMotion.FIRHoldWitness
example : |biasedReference (1/100) (171/50) 0| ≤ 0 := by
  rw [biased_terminal_not_exact_goal]
  norm_num
