import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : edgeCost FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) = normalizedEdgeCostQ FiniteProfileControls.oneEdge (FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ))) := by
 have h := Erdos128.FinalControls.missing_order_square_control
 simp_all
