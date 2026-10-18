import HodgeChecks
open GUHodgeBridge
example : H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = e 2 I01 := by
  exact H_square (e 2 I01)
