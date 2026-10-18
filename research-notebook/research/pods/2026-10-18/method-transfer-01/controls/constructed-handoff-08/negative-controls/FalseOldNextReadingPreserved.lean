import HandoffWitness
open LeanControls.ConstructedHandoff LeanControls.ConstructedHandoff.Witness
example : newReadings oldReads localHold 632 noise 633 2=oldReads 633 2 := by
 have hh := fresh_next_reading
 linarith
