import TimingEntry
open LeanControls.TimingClock
example : stamp false (dispatch 1)=sample 1 := by
 rw [second_dispatch_sides.1]
 norm_num [sample]
