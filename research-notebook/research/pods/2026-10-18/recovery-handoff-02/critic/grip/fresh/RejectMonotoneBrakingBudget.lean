import Recovery
open LeanControls.Recovery
example : travelBudget (1/100) 0 0 2 8 ≤ travelBudget (1/100) 0 0 1 8 := by
 norm_num [travelBudget,velocityBudget]
