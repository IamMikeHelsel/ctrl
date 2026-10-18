import DigitalHold
open LeanControls.DigitalHold
example : (111/1000:ℝ)≤2*radius-1/10000 := by norm_num [radius]
