import ReviewControls
open E10
example : Mem (Expr.val (1/2) 0 (.recip .c)) (Expr.box (-1,1) (0,0) (.recip .c)) := by
  norm_num [E10.Mem, Expr.val, Expr.box, E10.inv]
