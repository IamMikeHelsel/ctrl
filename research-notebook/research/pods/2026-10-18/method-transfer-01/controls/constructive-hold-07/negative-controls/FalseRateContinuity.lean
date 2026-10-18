import ConstructiveWitness
open LeanControls.ConstructiveHold LeanControls.ConstructiveHold.Witness
example : field (fun _ _ => 8) rates false (grid 2)=field (fun _ _ => 8) rates true (grid 2) := by
 rw [actual_rate_and_error_jump.1,actual_rate_and_error_jump.2.1]
 norm_num
