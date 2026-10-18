import DelayedWitness
open LeanControls
example : AdaptiveAdmission.center AdaptiveAdmission.exampleReading+DigitalHold.radius ≤ 3/20 := by
 norm_num [AdaptiveAdmission.center,AdaptiveAdmission.exampleReading,DigitalHold.radius]
