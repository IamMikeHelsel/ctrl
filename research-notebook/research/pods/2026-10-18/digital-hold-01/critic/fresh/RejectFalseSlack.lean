import DigitalHold
open LeanControls.DigitalHold
example : (103621708/1000000000:ℝ) + 98304/1000000*radius ≤ 2*radius-1/500 := by
  norm_num [radius]
