import FiniteControls
open Erdos128 Erdos128.FiniteProfileBridge Erdos128.FiniteProfileControls
example : (5 / 6 : ℚ) ^ 2 * (-1 / 15) * ((1 / 6) / (5 / 6) - 2 * ((1 / 36) / (5 / 6) ^ 2)) =
  (-1 / 15) * ((1 / 6) - meanDegree (5 / 6) (1 / 36)) := by
  norm_num [meanDegree]
