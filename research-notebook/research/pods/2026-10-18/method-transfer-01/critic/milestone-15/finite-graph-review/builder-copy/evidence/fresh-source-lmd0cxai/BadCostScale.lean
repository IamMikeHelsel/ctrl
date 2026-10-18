import FiniteControls
open Erdos128 Erdos128.FiniteProfileBridge Erdos128.FiniteProfileControls
example : sideMass cut * weightedObjective cut.largeGraph cut.uniformLargeWeight (fun _ => 0)
  (fun _ => (3 / 5 : ℚ)) = normalizedEdgeCostQ oneEdge (cut.extendLarge (fun _ => (3 / 5 : ℚ))) := by
  have h := wrong_cost_scale.2
  simp_all
