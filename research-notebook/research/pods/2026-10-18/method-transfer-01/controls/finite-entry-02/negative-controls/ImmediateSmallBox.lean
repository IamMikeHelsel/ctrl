import WeightedEntry
open LeanControls.WeightedEntry LeanControls.DigitalHold
example : weightedRadius (coordinates 0 ![0,0,16*radius]) ≤ target := by
 have h := old_initial_not_small.2
 linarith
