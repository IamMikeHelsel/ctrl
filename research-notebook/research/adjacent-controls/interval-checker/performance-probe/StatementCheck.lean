import IntervalPilot
import KernelFin
import KernelSplit

namespace LeanControls.PerformanceProbe.StatementCheck
open IntervalChecker

theorem identical_coefficients : KernelSplit.coeff = IntervalPilot.coeff := rfl
theorem identical_boxes : KernelSplit.boxes = IntervalPilot.boxes := rfl

/-- The new proof inhabits precisely the original pilot's step statement. -/
theorem same_checked_steps : ∀ n<25,
    BoxSubset (sampledBox IntervalPilot.coeff (IntervalPilot.boxes n) (point 0) (point 0))
      (IntervalPilot.boxes (n+1)) := by
  exact KernelSplit.checked_steps

theorem same_endpoints {r : ℝ} {z : UncertainLag.State}
    (hk : CoeffMem IntervalPilot.coeff r (1/20))
    (hz : BoxMem (IntervalPilot.boxes 0) z) :
    ∀ n≤25, BoxMem (IntervalPilot.boxes n)
      (stateTrace (fun _=>r) (fun _=>1/20) (fun _=>0) (fun _=>0) z n) := by
  exact KernelSplit.endpoints hk hz

end LeanControls.PerformanceProbe.StatementCheck
#print axioms LeanControls.PerformanceProbe.StatementCheck.identical_coefficients
#print axioms LeanControls.PerformanceProbe.StatementCheck.identical_boxes
#print axioms LeanControls.PerformanceProbe.StatementCheck.same_checked_steps
#print axioms LeanControls.PerformanceProbe.StatementCheck.same_endpoints
