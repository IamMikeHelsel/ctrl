import QuadraticWitness
open LeanControls.QuadraticWitness
example : |movingState 0 1| ≤ 1/1000 ∧ |movingState 0 2| ≤ 1/50 := by
  norm_num [movingState]
