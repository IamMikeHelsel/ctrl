import ReviewControls
open DetectorReview LeanControls
example : ClearancePolicy.Guard (earlyState (8/25)) → earlyState (8/25) 1 ≤ 0 := by
  intro hg
  norm_num [earlyState,UncertainLag.heldSolution]
