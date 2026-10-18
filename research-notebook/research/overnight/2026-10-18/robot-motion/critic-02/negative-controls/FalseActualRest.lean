import ReviewRestBoundary
open IndependentMotionReview02
example : drift (17/10) 1 = 0 := by
  rw [actual_terminal_velocity_not_zero]
  norm_num
