import ClearanceWitness
open LeanControls.ClearanceAdmission LeanControls.ClearanceAdmission.Witness
example : actualCommand delay (center exampleReading) (fun _ _ => exampleReading) false delay = 3635533/12500000 := by
 have h := actual_command_jump.1
 linarith
