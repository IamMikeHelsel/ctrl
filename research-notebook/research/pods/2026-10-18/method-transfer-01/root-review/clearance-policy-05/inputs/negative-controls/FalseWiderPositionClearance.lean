import ClearanceWitness
open LeanControls.ClearancePolicy
example : center ![144/1000,561/50000,-127/100]+(51/50)*policyRadius ![144/1000,561/50000,-127/100] ≤ 3/20 := by
 norm_num [center,policyRadius,max3,pair,offsets,error,LeanControls.WeightedEntry.weight,LeanControls.WeightedEntry.target]
