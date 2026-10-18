import DetectorWitness
open LeanControls.DetectorWitness LeanControls.UncertainLag LeanControls.ClearancePolicy
example : Guard (fast (1/250)) := by
 norm_num [Guard,fast,heldSolution]
