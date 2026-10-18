import DelayedWitness
open LeanControls.DelayedEntry.Witness
example : 0 ≤ stamp false delay-delay := by
 have h := illegal_reset_makes_negative_stamp
 linarith
