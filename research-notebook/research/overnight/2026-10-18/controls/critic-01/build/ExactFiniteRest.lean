import ReviewWitnesses
open LeanControls.SettlingIndependentReview
example : physicalNonrest (1/5000) 2 1 = 0 := by
  norm_num [physicalNonrest, Real.exp_ne_zero]
