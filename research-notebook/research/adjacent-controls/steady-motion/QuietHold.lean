module
public import CommitmentGate
public import RobustHold
@[expose] public section
noncomputable section
namespace LeanControls.QuietHold
open Set
open UncertainLag (State)
open VariableResponse RobustHold CommitmentGate

/-- The actual plant uses the gated reference. For a fixed true target and valid
bounded-noise proposals, the gate never moves that reference. The physical plant
then retains its robust tube and input-authority bound at every time in the horizon.
This is bounded position holding; velocity may be nonzero inside the tube.
`sampleCount` permits any schedule. No proposal can change the reference here. -/
theorem noisy_replans_preserve_hold {T R c p ε threshold U : ℝ}
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    {y : ℕ → ℝ} {sampleCount : ℝ → ℕ}
    (hc : |c-p| ≤ ε) (hy : ∀ k, |y k-p| ≤ ε) (hg : 2*ε ≤ threshold)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory T r
      (fun t => command (history y c threshold (sampleCount t)) (f t) + w t) f)
    (hrlo : ∀ t ∈ Icc 0 T, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 T, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 T, |w t| ≤ 2*R)
    (hi : ∀ i, |coordinates c (f 0) i| ≤ R) (hu : 26*R ≤ U) :
    (∀ n, history y c threshold n = c) ∧
    (∀ t ∈ Icc 0 T, |f t 0-p| ≤ R+ε ∧
      |command (history y c threshold (sampleCount t)) (f t)+w t| ≤ U) := by
  have hhist : ∀ n, history y c threshold n = c :=
    fun n => fixed_target_history hc hy hg n
  have hf' : IsTrajectory T r (fun t => command c (f t)+w t) f := by
    simpa only [hhist] using hf
  refine ⟨hhist, ?_⟩
  intro t ht
  have hb := actual_hold_bounds hT hR hf' hrlo hrhi hw hi t ht
  constructor
  · calc |f t 0-p| = |(f t 0-c)+(c-p)| := by congr 1; ring
         _ ≤ |f t 0-c|+|c-p| := abs_add_le _ _
         _ ≤ R+ε := add_le_add hb.1 hc
  · simpa only [hhist] using le_trans hb.2.2 hu
end LeanControls.QuietHold
