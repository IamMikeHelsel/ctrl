import QuadraticWitness
open LeanControls.QuadraticHold
example : energy 16 0 0 ≤ 1 := by
  norm_num [energy]
