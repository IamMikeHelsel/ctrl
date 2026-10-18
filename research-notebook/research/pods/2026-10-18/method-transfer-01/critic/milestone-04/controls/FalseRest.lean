import LateBoxScope
open CriticLateBox
example : testState 1 = 0 := by
  have h := weighted_box_allows_motion.2.2
  linarith
