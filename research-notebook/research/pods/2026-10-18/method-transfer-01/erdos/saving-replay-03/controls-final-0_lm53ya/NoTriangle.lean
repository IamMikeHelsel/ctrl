import MeaningfulControls
open Erdos128 SavingReplayControls
open scoped BigOperators
noncomputable section
example : (1 / 18 : ℚ) ≤
    weightedObjective triangle thirds (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
      4 * savingLQ (1 / 2) * edgeMass triangle thirds ^ 3 := by
  rw [triangle_budget]
  norm_num
