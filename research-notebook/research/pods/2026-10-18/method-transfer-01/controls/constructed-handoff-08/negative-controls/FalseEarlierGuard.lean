import HandoffWitness
open LeanControls.ConstructedHandoff.Witness LeanControls.DetectorSampling
example : LeanControls.ClearancePolicy.Guard (oldReads 631) := by
 norm_num [LeanControls.ClearancePolicy.Guard,oldReads,early,DetectorReview.earlyState,LeanControls.UncertainLag.heldSolution,sample]
