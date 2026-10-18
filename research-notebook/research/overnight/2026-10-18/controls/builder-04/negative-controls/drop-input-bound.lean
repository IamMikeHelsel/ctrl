import QuadraticWitness
open LeanControls.QuadraticHold
example : energyRate 80 2 2 0 0 ≤ 20*(1-energy 2 0 0) := by
  norm_num [energyRate,energy]
