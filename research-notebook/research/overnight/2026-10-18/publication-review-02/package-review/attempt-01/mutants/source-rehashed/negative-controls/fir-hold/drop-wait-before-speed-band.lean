import FIRHoldWitness
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.FIRHoldWitness
example : |biasedReference (1/100) (1/2) 1| ≤ 1/1000 := by
  norm_num [biasedReference,velocity,response,realEvents,realEvent,deferredReturn,F1,P]
