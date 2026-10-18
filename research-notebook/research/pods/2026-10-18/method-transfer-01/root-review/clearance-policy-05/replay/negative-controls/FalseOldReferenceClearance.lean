import ClearanceWitness
open LeanControls.ClearancePolicy
example : (323/3200)+(51/50)*fixedRadius nominal (323/3200) ≤ 3/20 := by
 have h := fair_nominal_baseline.2.2
 linarith
