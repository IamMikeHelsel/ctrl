import MeaningfulControls
open Erdos128 SavingReplayControls
open scoped BigOperators
noncomputable section
example :
    weightedObjective edge halves (fun _ => 0) (fun _ => (1 / 2 : ℚ)) ≤
      weightedObjective edge halves (fun _ => 0) (fun _ => (1 / 2 : ℚ)) -
        4 * savingLQ (1 / 2) * edgeMass edge halves ^ 3 := by
  classical
  norm_num [weightedObjective, edge, halves, weightedMean, edgeMass,
    weightedDegree, savingLQ, centerRadiusQ,
    SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter, Finset.filter_ne,
    Fin.sum_univ_succ]
