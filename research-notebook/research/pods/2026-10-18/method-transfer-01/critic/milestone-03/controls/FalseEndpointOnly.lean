import EndpointTrap
open LeanControls LeanControls.UncertainLag CriticEndpointTrap
example : ∀ s ∈ Set.Icc (0:ℝ) 1,
    heldSolution 8 s (-6/5) StoppingCertificate.engagementUpper 0 ≤ (7/50:ℝ) := by
  intro s hs
  have hp := endpoint_is_small_but_earlier_peak_is_not.1
  have hv := endpoint_is_small_but_earlier_peak_is_not.2.1
  linarith
