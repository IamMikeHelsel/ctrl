import DelayedWitness
open LeanControls
example : AdaptiveAdmission.actualCommand DelayedEntry.Witness.delay
    (AdaptiveAdmission.center (DelayedEntry.Witness.reading 0))
    (fun _ _ => DelayedEntry.Witness.reading 0) false DelayedEntry.Witness.delay = 0 := by
 have h := (DelayedEntry.Witness.dispatch_command_sides 0).1
 linarith
