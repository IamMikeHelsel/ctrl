import HodgeChecks
import HodgeInterface
open GUHodgeBridge
example : e 2 I01 ≠ 0 := I01_form_nonzero
example : H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = -(e 2 I01) := H_square _
example : ¬ (H (by decide : 12+2=14) (H (by decide : 2+12=14) (e 2 I01)) = e 2 I01) := H_square_not_positive_I01
example (x : E 2) : coordinates 12 (H (by decide : 2+12=14) x) = GUOperatorAudit.linearCoeff mathlibStar2 (coordinates 2 x) := frozen_interface_represents x
