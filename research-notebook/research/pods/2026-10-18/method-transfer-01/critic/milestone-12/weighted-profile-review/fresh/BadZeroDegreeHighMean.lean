import CriticControls
open Erdos128 Erdos128.ProfileBridge Erdos128.ProfileControls CriticE8
example : weightedMean singletonWeight (highProfile emptyGraph singletonWeight (4 / 5) 0) = 4 / 5 := by
  rw [zero_degree_high_mean]
  norm_num
