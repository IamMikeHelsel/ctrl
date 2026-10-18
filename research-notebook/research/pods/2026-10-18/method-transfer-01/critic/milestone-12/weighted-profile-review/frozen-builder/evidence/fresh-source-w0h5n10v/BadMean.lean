import ProfileControls
open Erdos128 Erdos128.ProfileControls
example : weightedMean halves (fun v : Fin 2 => if v = 0 then 4 / 5 else 0) = 4 / 5 := by
  norm_num [weightedMean, halves, Fin.sum_univ_succ]
