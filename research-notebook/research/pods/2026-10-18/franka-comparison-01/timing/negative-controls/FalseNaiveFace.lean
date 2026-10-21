import TimingEntry
open LeanControls.DigitalHold LeanControls.WeightedEntry
example : transformedRHS 12 (115/1000) ![-(51/50)*target,(101/100)*target,target] 2≤0 := by
 norm_num [transformedRHS,target]
