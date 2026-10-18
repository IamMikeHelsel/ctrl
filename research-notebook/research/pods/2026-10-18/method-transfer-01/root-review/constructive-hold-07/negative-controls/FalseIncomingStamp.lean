import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : stamp false (grid 2)=h := by
 have hs := second_dispatch_stamps.1
 norm_num [hs] 
