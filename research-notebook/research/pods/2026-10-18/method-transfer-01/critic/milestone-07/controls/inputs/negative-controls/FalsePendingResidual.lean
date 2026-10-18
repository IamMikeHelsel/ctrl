import DelayedWitness
open LeanControls
example : |AdaptiveAdmission.actualMismatch DelayedEntry.Witness.delay
    (DelayedEntry.Witness.reading 0) (DelayedEntry.Witness.state 0)
    (fun _ _ => 0) (fun _ _ => DelayedEntry.Witness.reading 0) false 0| ≤ DelayedEntry.residual := by
 have h := DelayedEntry.Witness.pending_mismatch_is_not_digital_budget 0
 linarith
