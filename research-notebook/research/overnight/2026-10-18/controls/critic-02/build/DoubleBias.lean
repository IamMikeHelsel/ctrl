import BiasWitness
open LeanControls.Settling LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.ConstantBias LeanControls.BiasWitness
example : 80*(holdInput 10 (offset 10 (1/100)) biasedRest 0+(1/100:ℝ)-biasedRest 0 2) = 0 := by
  norm_num [holdInput,command,scaleState,offset,biasedRest]
