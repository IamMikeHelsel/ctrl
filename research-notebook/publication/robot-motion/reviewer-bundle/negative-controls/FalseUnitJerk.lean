import RationalGuard
open RobotMotion
namespace RobotMotionNegative
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- False constant1 in place of the unit-step jerk peak2.
#eval qJerk 1 [(0,1)] 2
example : |qJerk 1 [(0,1)] 2| ≤ 1 := by decide +kernel
end RobotMotionNegative
