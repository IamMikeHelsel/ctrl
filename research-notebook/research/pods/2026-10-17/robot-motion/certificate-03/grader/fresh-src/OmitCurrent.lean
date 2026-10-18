import RationalGuard
open RobotMotion
namespace RobotMotionNegative
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Actual implementation mutation: delete c from the executable guard list.
def mutatedCheck (h J c : ℚ) (es : List QEvent) : Bool :=
  decide (0 < h ∧ 0 ≤ J) && ((qRoots h es).filter (fun t => decide (c ≤ t))).all
    (fun t => decide (|qJerk h es t| ≤ J))
#eval (mutatedCheck 1 (1/4) (7/2) [(0,1)], qJerk 1 [(0,1)] (7/2))
-- The required rejection fixture must fail for this mutant.
example : mutatedCheck 1 (1/4) (7/2) [(0,1)] = false := by decide +kernel
end RobotMotionNegative
