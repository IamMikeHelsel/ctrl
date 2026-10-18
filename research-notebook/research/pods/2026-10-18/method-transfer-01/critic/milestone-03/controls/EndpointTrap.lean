module
public import RecoveryPeak
@[expose] public section
noncomputable section
namespace CriticEndpointTrap
open LeanControls.UncertainLag LeanControls.RecoveryPeak
open LeanControls

/-- The actual same analytic upper flow defeats an endpoint-only peak test. -/
theorem endpoint_is_small_but_earlier_peak_is_not :
    heldSolution 8 1 (-6/5) StoppingCertificate.engagementUpper 0 < 0 ∧
    heldSolution 8 1 (-6/5) StoppingCertificate.engagementUpper 1 < 0 ∧
    (7/50:ℝ) < heldSolution 8 (12/25) (-6/5) StoppingCertificate.engagementUpper 0 := by
  have he0 := Real.exp_nonneg (-8:ℝ)
  have he1 : Real.exp (-8:ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  refine ⟨?_,?_,old_upper_exceeds_14cm⟩ <;>
    norm_num [heldSolution, StoppingCertificate.engagementUpper] <;> linarith
end CriticEndpointTrap
