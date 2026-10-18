import WeightedEntry
open LeanControls.WeightedEntry LeanControls.DigitalHold
example : transformedRHS 8 0 ![target,target,target] 0 ≤ -drift := by
 norm_num [transformedRHS,target,drift]
