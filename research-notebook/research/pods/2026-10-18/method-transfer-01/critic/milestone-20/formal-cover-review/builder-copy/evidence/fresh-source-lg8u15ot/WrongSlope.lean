import SelectorControls
open E10 E10.Controls Erdos128.FiniteProfileBridge
example : highCertificate (1/(2*cm)) jm R (Expr.slope cm jm 0) ≤ 0 := by
 have h := matched_slope_needed.2.2.1
 simp_all only [not_le_of_gt h]
