import FIRHoldWitness
open RobotMotion.FIRHoldWitness
example : biasedReference (1/100) (71/50) 0 = 0 := by
  rw [biased_endpoint_not_reset]
  norm_num
