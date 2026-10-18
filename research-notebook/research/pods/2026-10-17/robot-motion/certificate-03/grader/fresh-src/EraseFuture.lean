import RationalGuard
open RobotMotion
namespace RobotMotionNegative
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Actual implementation mutation: discard queued events after accepting the full candidate.
def mutatedCommit (h J c : ℚ) (es : List QEvent) : List QEvent :=
  if check h J c es then es.filter (fun e => decide (e.1 ≤ c)) else es
#eval (check 1 1 0 [(0,1),(1/4,-1)],
  check 1 1 0 (mutatedCommit 1 1 0 [(0,1),(1/4,-1)]))
example : check 1 1 0 (mutatedCommit 1 1 0 [(0,1),(1/4,-1)]) = true := by decide +kernel
end RobotMotionNegative
