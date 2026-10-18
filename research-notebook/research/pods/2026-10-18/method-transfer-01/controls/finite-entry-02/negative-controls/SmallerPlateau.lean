import WeightedEntry
open LeanControls.WeightedEntry LeanControls.DigitalHold
example : transformedRHS 12 residual ![-(51/50)*(1/25),(101/100)*(1/25),1/25] 2 ≤ 0 := by
 have h := smaller_plateau_outward
 linarith
