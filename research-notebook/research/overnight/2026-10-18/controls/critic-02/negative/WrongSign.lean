import BiasWitness
open LeanControls.UncertainLag LeanControls.Settling LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.ConstantBias
example : holdInput 10 0 (fun _ => (![0,0,0] : State)) 0+(1/100:ℝ) =
  holdInput 10 (0-offset 10 (1/100)) (fun _ => (![0,0,0] : State)) 0 := by
  norm_num [holdInput,command,scaleState,offset]
