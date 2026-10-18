import SelectorControls
namespace E10.Review

/-- Dropping Expr.safe is unsound across zero, even at a nonzero point. -/
theorem reciprocal_guard_essential :
    Mem (1/2 : ℚ) (-1,1) ∧
    Expr.safe (-1,1) (0,0) (.recip .c) = false ∧
    ¬ Mem (Expr.val (1/2) 0 (.recip .c)) (Expr.box (-1,1) (0,0) (.recip .c)) := by
  norm_num [E10.Mem, Expr.safe, Expr.val, Expr.box, E10.inv]

end E10.Review
#print axioms E10.Review.reciprocal_guard_essential
