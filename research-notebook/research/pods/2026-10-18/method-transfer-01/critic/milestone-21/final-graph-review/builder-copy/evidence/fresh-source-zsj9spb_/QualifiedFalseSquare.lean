import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : (E10.sq (-1,2)).1=1 := by
 norm_num [E10.sq]
