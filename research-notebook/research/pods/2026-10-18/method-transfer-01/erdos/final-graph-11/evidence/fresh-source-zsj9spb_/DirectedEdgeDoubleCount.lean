import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : (∑ u : Fin 6, ∑ v : Fin 6, if FiniteProfileControls.oneEdge.Adj u v then FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)) u * FiniteProfileControls.cut.extendLarge (fun _ => (3/5:ℚ)) v else 0) = 9/25 := by
 rw [Erdos128.FinalControls.directed_edge_count_control]
 norm_num
