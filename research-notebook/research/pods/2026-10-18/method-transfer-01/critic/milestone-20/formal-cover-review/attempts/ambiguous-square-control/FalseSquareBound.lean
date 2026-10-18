import SelectorControls
open E10 E10.Controls Erdos128.FiniteProfileBridge
example : (sq (-1,2)).1 = 1 := by
 norm_num [sq]
