import HandoffWitness
open LeanControls.ConstructiveHold LeanControls.ConstructedHandoff.Witness
example : grid 632+stamp false (grid 2)=grid 633 := by
 rw [absolute_dispatch_stamps.1]
 norm_num [grid]
