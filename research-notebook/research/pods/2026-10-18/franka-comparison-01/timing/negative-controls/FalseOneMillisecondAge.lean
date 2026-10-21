import TimingEntry
open LeanControls.TimingClock
example : dispatch 1-stamp false (dispatch 1)≤1/1000 := by
 rw [second_dispatch_sides.2.2.1]
 norm_num
