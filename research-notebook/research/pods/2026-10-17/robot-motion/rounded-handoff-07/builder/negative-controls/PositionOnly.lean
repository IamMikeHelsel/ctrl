import HandoffWitnesses
open LeanControls LeanControls.RobustHold LeanControls.ScaledTracking LeanControls.HandoffWitnesses
example : |coordinates 0 (scaleState 10 (velocityOnly 0-rest 0)) 2| ≤ (0:ℝ) := by
  norm_num [velocityOnly,rest,coordinates,scaleState]
