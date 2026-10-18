import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : LeanControls.ClearanceAdmission.actualCommand h (LeanControls.ClearanceAdmission.center m) (readings m noise run) false h=
 LeanControls.ClearanceAdmission.actualCommand h (LeanControls.ClearanceAdmission.center m) (readings m noise run) true h := by
 rw [first_command_jump.1,first_command_jump.2]
 norm_num
