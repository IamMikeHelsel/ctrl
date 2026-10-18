import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : (0:ℚ)<(Fintype.card (Fin 0):ℚ)^2 := by
 norm_num
