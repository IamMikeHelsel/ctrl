import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : (1/2:ℚ)<sideMass Erdos128.FinalControls.balancedCut := by
 rw [Erdos128.FinalControls.balanced_parameters.2.1]
 norm_num
