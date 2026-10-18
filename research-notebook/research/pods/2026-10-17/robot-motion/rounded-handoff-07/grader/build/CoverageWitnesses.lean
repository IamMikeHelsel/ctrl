import NativeCoverage
namespace IndependentCoverageReview
open NativeRational
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem enlarged_horizon_is_rejected : check 3 hold_jitter__ruckig = false := by decide +kernel
theorem missing_initial_interval_is_rejected : check (5/2) (hold_jitter__ruckig.drop 1) = false := by decide +kernel
end IndependentCoverageReview
