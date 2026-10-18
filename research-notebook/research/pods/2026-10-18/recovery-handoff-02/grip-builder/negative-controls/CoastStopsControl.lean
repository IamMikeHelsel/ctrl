import Recovery
open LeanControls.Recovery
example : ∃ t : ℝ, coast t 1 ≤ 0 := by
  norm_num [coast]
