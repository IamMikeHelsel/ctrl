module
public import ClearancePolicy
@[expose] public section
noncomputable section
namespace S11Face
open LeanControls.DigitalHold LeanControls.WeightedEntry

/-- Actual r=12 third upper face of the unchanged transformed hold law. -/
theorem exact_upper_face (K W : ℝ) :
    transformedRHS 12 W ![-(51/50)*K,(101/100)*K,K] 2 =
      -(19/10)*K+(3/4)*W := by
  norm_num [transformedRHS]
  ring

/-- A necessary inward-face condition for this complete weighted box, not for
all possible terminal sets or correlated residual sets. -/
theorem inward_requires_residual (K W : ℝ)
    (h : transformedRHS 12 W ![-(51/50)*K,(101/100)*K,K] 2 ≤ 0) :
    W ≤ (38/15)*K := by
  rw [exact_upper_face] at h
  linarith

theorem millimeter_speed_requires_residual (K W : ℝ)
    (h : transformedRHS 12 W ![-(51/50)*K,(101/100)*K,K] 2 ≤ 0)
    (hv : (203/25)*K ≤ (1/1000 : ℝ)) :
    W ≤ (19/60900 : ℝ) := by
  have hh := inward_requires_residual K W h
  linarith

theorem physical_uncertainty_exceeds_budget :
    (19/60900 : ℝ)<1/100 := by norm_num

#print axioms exact_upper_face
#print axioms inward_requires_residual
#print axioms millimeter_speed_requires_residual
#print axioms physical_uncertainty_exceeds_budget
end S11Face
