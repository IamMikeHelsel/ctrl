import HandoffWitness
open LeanControls.ConstructiveHold LeanControls.ConstructedHandoff.Witness
example : run (grid 632+h) 1=0 := by
 rw [positive_arrival.1]
 norm_num
