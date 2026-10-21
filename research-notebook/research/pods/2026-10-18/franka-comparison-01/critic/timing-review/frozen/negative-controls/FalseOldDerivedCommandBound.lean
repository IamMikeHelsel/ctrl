import TimingEntry
open LeanControls.TimingBudget
example : 24*supportRadius+noise≤3589/2500 := by
 norm_num [supportRadius,noise]
