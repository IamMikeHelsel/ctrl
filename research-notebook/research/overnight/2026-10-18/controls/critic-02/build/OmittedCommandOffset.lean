import BiasWitness
open LeanControls.Settling LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.BiasWitness
example : |holdInput 10 0 biasedRest 2| ≤ 24*(10:ℝ)^2*(17/16384000) := by
  norm_num [holdInput,command,scaleState,biasedRest]
