import Submission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
theorem test6 : Submission.impl 25769803776 = 16 := by rfl
theorem test12 : Submission.impl 51539607552 = 74 := by rfl
theorem test16 : Submission.impl 68719476736 = 154 := by rfl
