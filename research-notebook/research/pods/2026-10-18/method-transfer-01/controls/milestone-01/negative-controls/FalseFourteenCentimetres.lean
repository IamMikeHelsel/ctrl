import RecoveryPeak
open LeanControls.RecoveryPeak LeanControls.UncertainLag
example : heldSolution 8 (12/25) (-6/5) LeanControls.StoppingCertificate.engagementUpper 0 ≤ (7/50:ℝ) := by
 have h := old_upper_exceeds_14cm
 nlinarith
