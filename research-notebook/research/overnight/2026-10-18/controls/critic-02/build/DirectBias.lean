module
public import BiasFixtures
public import DirectReference
@[expose] public section
noncomputable section
namespace LeanControls.DirectBias
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling ConstantBias BiasFixtures

/-- The original actual endpoint enters the original holding controller.
The constant-bias assumption applies only to this final hold. -/
theorem fixed_reference_then_bias_hold
    {previous : ℕ → ℝ → State} {rp wp : ℕ → ℝ → ℝ}
    (hp : DirectReference.DirectPlant previous rp wp)
    {H b : ℝ} (hH : 2 ≤ H) (hb : |b| ≤ 1/100)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 (3/5) f t+b) f)
    (hmatch : f 0 = previous 7 (DirectReference.duration 7))
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120) :
    ∀ t ∈ Icc 2 H,
      |f t 0-3/5| ≤ 1109/81920000 ∧
      |f t 1| ≤ 17/204800 ∧ |f t 2| ≤ 17/2560 := by
  apply two_second_actual hH hb hf hrlo hrhi
  exact matched_hold_cube hmatch DirectReference.reference_endpoint
    (DirectReference.direct_cube hp 7 (by norm_num) (DirectReference.duration 7)
      ⟨(DirectReference.duration_positive 7 (by norm_num)).le,le_rfl⟩)

theorem fixed_reference_bias_endpoint
    {previous : ℕ → ℝ → State} {rp wp : ℕ → ℝ → ℝ}
    (hp : DirectReference.DirectPlant previous rp wp)
    {H b : ℝ} (hH : 2 ≤ H) (hb : |b| ≤ 1/100)
    {r : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r (fun t => holdInput 10 (3/5) f t+b) f)
    (hmatch : f 0 = previous 7 (DirectReference.duration 7))
    (hrlo : ∀ t ∈ Icc 0 H, 80 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 120) :
    |f 2 0-3/5| ≤ 1109/81920000 ∧
      |f 2 1| ≤ 17/204800 ∧ |f 2 2| ≤ 17/2560 :=
  fixed_reference_then_bias_hold hp hH hb hf hmatch hrlo hrhi 2 ⟨le_rfl,hH⟩

end LeanControls.DirectBias
