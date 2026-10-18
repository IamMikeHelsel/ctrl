import NativeCoverage

noncomputable section
namespace NativeRational
open Set
open LeanControls
open LeanControls.UncertainLag (State)
open LeanControls.VariableResponse LeanControls.RobustHold
open LeanControls.TrackingReplan LeanControls.ScaledTracking LeanControls.RoundedHandoff

/-- The checked schedule supplies a valid local piece and a physical position
tracking bound at every absolute time in its closed horizon. All actual plant
premises remain explicit; no independent tracking certificate is assumed. -/
theorem checked_absolute_position_tracking {H : ℚ} {xs : List Piece}
    (h : check H xs = true) (hlen : xs.length ≤ 189)
    {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (hf : ∀ k < xs.length, IsTrajectory (realDuration xs k) (r k)
      (fun t => physicalInput 10 (f k) (reference (realZ xs k) (realJerk xs k))
        (fun _ => realJerk xs k) t + w k t) (f k))
    (hrlo : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), 80 ≤ r k t)
    (hrhi : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), r k t ≤ 120)
    (hw : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), |w k t| ≤ 1/100)
    (hphysical : ∀ k, k+1 < xs.length → f (k+1) 0 = f k (realDuration xs k))
    (hi : ∀ i, |coordinates 0 (scaledError 10 (f 0)
      (reference (realZ xs 0) (realJerk xs 0)) 0) i| ≤ 41/320000) :
    ∀ time ∈ Icc 0 (H : ℝ), ∃ k, k < xs.length ∧
      time ∈ Icc ((pieceAt xs k).start : ℝ) ((pieceAt xs k).finish : ℝ) ∧
      |f k (time-((pieceAt xs k).start : ℝ)) 0 -
        reference (realZ xs k) (realJerk xs k)
          (time-((pieceAt xs k).start : ℝ)) 0| ≤
        41/320000 + 188/1000000000000000 := by
  intro time ht
  obtain ⟨k,hk,hinterval,hoffset⟩ := checked_local_offset h ht
  exact ⟨k,hk,hinterval,checked_position_tracking h hlen hf hrlo hrhi hw
    hphysical hi k hk _ hoffset⟩

end NativeRational
