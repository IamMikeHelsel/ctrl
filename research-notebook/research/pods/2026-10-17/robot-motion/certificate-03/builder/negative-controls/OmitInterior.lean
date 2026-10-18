import RationalGuard
open RobotMotion
namespace RobotMotionNegative
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Actual implementation mutation: retain only start and tail roots.
def mutatedRoots (h : ℚ) (es : List QEvent) : List ℚ :=
  es.flatMap (fun e => [e.1,e.1+4*h])
def mutatedCheck (h J c : ℚ) (es : List QEvent) : Bool :=
  decide (0 < h ∧ 0 ≤ J) && (c :: (mutatedRoots h es).filter (fun t => decide (c ≤ t))).all
    (fun t => decide (|qJerk h es t| ≤ J))
#eval (mutatedCheck 1 1 0 [(0,1)], qJerk 1 [(0,1)] 2)
example : mutatedCheck 1 1 0 [(0,1)] = false := by decide +kernel
end RobotMotionNegative
