import TimingEntry
open LeanControls.DigitalHold LeanControls.WeightedEntry
example : transformedRHS 12 LeanControls.TimingBudget.residual ![-(51/50)*target,(101/100)*target,target] 2≤-drift := by
 norm_num [transformedRHS,target,LeanControls.TimingBudget.residual,drift]
