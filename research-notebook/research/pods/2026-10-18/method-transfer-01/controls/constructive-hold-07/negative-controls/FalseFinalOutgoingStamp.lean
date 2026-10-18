import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : stamp false (grid 4)=grid 3 := by
 have hs := final_dispatch_stamps.1
 rw [hs]
 norm_num [grid]
