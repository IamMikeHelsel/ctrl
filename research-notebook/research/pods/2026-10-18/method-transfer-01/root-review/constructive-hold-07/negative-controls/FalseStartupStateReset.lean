import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : run h 2=run 0 2 := by
 have hs := changed_startup_state
 linarith
