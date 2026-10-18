import RecoveryPeakWitness
open LeanControls.RecoveryPeak.Witness LeanControls.UncertainLag
example : heldSolution 1 1 (-1) ![0,0,1] 1 = 0 := by
 have h := zero_speed_not_hold.2.1
 linarith
