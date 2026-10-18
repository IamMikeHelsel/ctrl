module
public import SettlingFixtures
public import DirectReference
@[expose] public section
noncomputable section
namespace LeanControls.DirectSettling
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures

/-- Continue the frozen eight-phase direct trajectory with its actual endpoint
state. No new initial-error assumption is used in this composition. -/
theorem fixed_reference_then_hold
    {previous : ℕ → ℝ → State} {rp wp : ℕ → ℝ → ℝ}
    (hp : DirectReference.DirectPlant previous rp wp)
    {H : ℝ} (hH : 0 ≤ H) {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 (3/5) f t+w t) f)
    (hmatch : f 0 = previous 7 (DirectReference.duration 7))
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ 1/100) :
    ∀ t ∈ Icc 1 H,
      |f t 0-3/5| ≤ 17/320000 ∧ |f t 1| ≤ 17/4000 ∧ |f t 2| ≤ 17/50 := by
  apply one_second_actual hH hf hrlo hrhi hw
  exact matched_hold_cube hmatch DirectReference.reference_endpoint
    (DirectReference.direct_cube hp 7 (by norm_num) (DirectReference.duration 7)
      ⟨(DirectReference.duration_positive 7 (by norm_num)).le,le_rfl⟩)

/-- If the final hold has no disturbance, the frozen direct motion reaches
the tighter physical speed and acceleration bands after two hold seconds. -/
theorem fixed_reference_then_zero_disturbance_hold
    {previous : ℕ → ℝ → State} {rp wp : ℕ → ℝ → ℝ}
    (hp : DirectReference.DirectPlant previous rp wp)
    {H : ℝ} (hH : 0 ≤ H) {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 (3/5) f t+(0:ℝ)) f)
    (hmatch : f 0 = previous 7 (DirectReference.duration 7))
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120) :
    ∀ t ∈ Icc 2 H,
      |f t 0-3/5| ≤ 1/1024000 ∧ |f t 1| ≤ 1/12800 ∧ |f t 2| ≤ 1/160 := by
  apply two_seconds_actual_zero_disturbance hH hf hrlo hrhi
  exact matched_hold_cube hmatch DirectReference.reference_endpoint
    (DirectReference.direct_cube hp 7 (by norm_num) (DirectReference.duration 7)
      ⟨(DirectReference.duration_positive 7 (by norm_num)).le,le_rfl⟩)

end LeanControls.DirectSettling
