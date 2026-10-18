import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : completionEnvelope (4:ℚ) 5 = 10*E10.completion (5/6) := by
 norm_num [completionEnvelope,E10.completion,E10.Q,E10.xval]
