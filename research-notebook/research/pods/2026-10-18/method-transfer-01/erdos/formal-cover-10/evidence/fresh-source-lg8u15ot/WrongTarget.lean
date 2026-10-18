import SelectorControls
open E10 E10.Controls Erdos128.FiniteProfileBridge
example : AtTarget r0 c0 j0 := by
 have h := wrong_target_counterexample.2.2.2.2
 simp_all
