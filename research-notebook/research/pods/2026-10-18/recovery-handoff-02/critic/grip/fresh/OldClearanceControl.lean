import Recovery
open LeanControls.Recovery
example : (1/1000:ℝ)+travelBudget (41/100) (1/10) (1/20) (6/5) 8 ≤ 3/20 := by
  norm_num [travelBudget, velocityBudget]
