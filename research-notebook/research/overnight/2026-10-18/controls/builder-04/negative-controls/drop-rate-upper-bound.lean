import QuadraticWitness
open LeanControls.QuadraticHold
example : energyRate 160 (-1) (-2) 2 (-1) ≤ 20*(1-energy (-2) 2 (-1)) := by
  norm_num [energyRate,energy]
