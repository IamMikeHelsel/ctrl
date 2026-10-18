import Settling
open LeanControls.UncertainLag
example : (3/1000:ℝ) ≤ |(![1/80000,0,0] : State) 1| := by
  norm_num
