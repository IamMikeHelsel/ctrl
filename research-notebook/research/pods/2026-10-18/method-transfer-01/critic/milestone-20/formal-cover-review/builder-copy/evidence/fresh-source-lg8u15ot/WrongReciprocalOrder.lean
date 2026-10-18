import SelectorControls
open E10 E10.Controls Erdos128.FiniteProfileBridge
example : Mem (1/(2:ℚ)) (1,1/2) := by
 norm_num [Mem]
