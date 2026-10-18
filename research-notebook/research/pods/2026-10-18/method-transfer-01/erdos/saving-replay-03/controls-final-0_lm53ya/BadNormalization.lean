import MeaningfulControls
open Erdos128 SavingReplayControls
open scoped BigOperators
noncomputable section
def invalidWeights : RatProbabilityWeight (Fin 2) where
  weight := fun _ => 1
  positive := by intro v; norm_num
  sum_eq_one := by norm_num
