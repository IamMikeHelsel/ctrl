import TimingEntry
open LeanControls.TimingBudget LeanControls.DigitalHold
example : splitResidual age delay radius≤2*radius := by
 norm_num [splitResidual,digitalSlope,firstResidual,coarseSlope,noise,age,delay,radius]
