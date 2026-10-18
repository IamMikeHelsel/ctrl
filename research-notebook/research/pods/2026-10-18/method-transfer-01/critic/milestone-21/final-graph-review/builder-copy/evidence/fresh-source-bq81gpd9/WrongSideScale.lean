import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : sideMass FiniteProfileControls.cut * weightedObjective FiniteProfileControls.cut.largeGraph FiniteProfileControls.cut.uniformLargeWeight (fun _ => 0) (fun _ => (3/5:ℚ)) = normalizedEdgeCostQ FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) := by
 have h := FiniteProfileControls.wrong_cost_scale.2
 simp_all
