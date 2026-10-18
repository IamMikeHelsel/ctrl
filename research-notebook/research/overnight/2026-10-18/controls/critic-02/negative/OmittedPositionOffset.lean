import BiasWitness
open LeanControls.BiasWitness
example : |biasedRest 2 0-(0:ℝ)| ≤ 17/16384000 := by
  norm_num [biasedRest]
