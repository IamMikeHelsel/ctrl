import DetectorWitness
open LeanControls.UncertainLag LeanControls.ClearancePolicy
example : Guard (heldSolution 8 (1/1000) (1/10) ![0,0,1/10]) := by
 norm_num [Guard,heldSolution]
