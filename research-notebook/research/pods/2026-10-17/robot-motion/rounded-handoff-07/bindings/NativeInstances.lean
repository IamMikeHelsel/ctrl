import NativeBridge

noncomputable section
namespace NativeRational
open Set LeanControls
open LeanControls.UncertainLag (State)
open LeanControls.VariableResponse LeanControls.RobustHold
open LeanControls.TrackingReplan LeanControls.ScaledTracking

def PositionCertificate (xs : List Piece) : Prop :=
    ∀ {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    (hf : ∀ k < xs.length, IsTrajectory (realDuration xs k) (r k)
      (fun t => physicalInput 10 (f k) (reference (realZ xs k) (realJerk xs k))
        (fun _ => realJerk xs k) t + w k t) (f k))
    (hrlo : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), 80 ≤ r k t)
    (hrhi : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), r k t ≤ 120)
    (hw : ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k), |w k t| ≤ 1/100)
    (hphysical : ∀ k, k+1 < xs.length → f (k+1) 0 = f k (realDuration xs k))
    (hi : ∀ i, |coordinates 0 (scaledError 10 (f 0)
      (reference (realZ xs 0) (realJerk xs 0)) 0) i| ≤ 41/320000),
    ∀ k < xs.length, ∀ t ∈ Icc 0 (realDuration xs k),
      |f k t 0 - reference (realZ xs k) (realJerk xs k) t 0| ≤
        41/320000 + 188/1000000000000000

theorem certificate_of_check {H : ℚ} {xs : List Piece}
    (h : check H xs = true) (hlen : xs.length ≤ 189) : PositionCertificate xs := by
  intro f r w hf hrlo hrhi hw hphysical hi
  exact checked_position_tracking h hlen hf hrlo hrhi hw hphysical hi

set_option maxRecDepth 100000

theorem hold_jitter__ruckig_certificate : PositionCertificate hold_jitter__ruckig :=
  certificate_of_check hold_jitter__ruckig_checked (by decide +kernel)

theorem hold_jitter__ruckig_min_08_certificate : PositionCertificate hold_jitter__ruckig_min_08 :=
  certificate_of_check hold_jitter__ruckig_min_08_checked (by decide +kernel)

theorem persistent_goal__ruckig_certificate : PositionCertificate persistent_goal__ruckig :=
  certificate_of_check persistent_goal__ruckig_checked (by decide +kernel)

theorem persistent_goal__ruckig_min_08_certificate : PositionCertificate persistent_goal__ruckig_min_08 :=
  certificate_of_check persistent_goal__ruckig_min_08_checked (by decide +kernel)

theorem sign_60ms__ruckig_certificate : PositionCertificate sign_60ms__ruckig :=
  certificate_of_check sign_60ms__ruckig_checked (by decide +kernel)

theorem sign_60ms__ruckig_min_08_certificate : PositionCertificate sign_60ms__ruckig_min_08 :=
  certificate_of_check sign_60ms__ruckig_min_08_checked (by decide +kernel)

theorem irregular_alternation__ruckig_certificate : PositionCertificate irregular_alternation__ruckig :=
  certificate_of_check irregular_alternation__ruckig_checked (by decide +kernel)

theorem irregular_alternation__ruckig_min_08_certificate : PositionCertificate irregular_alternation__ruckig_min_08 :=
  certificate_of_check irregular_alternation__ruckig_min_08_checked (by decide +kernel)

theorem seeded_random__ruckig_certificate : PositionCertificate seeded_random__ruckig :=
  certificate_of_check seeded_random__ruckig_checked (by decide +kernel)

theorem seeded_random__ruckig_min_08_certificate : PositionCertificate seeded_random__ruckig_min_08 :=
  certificate_of_check seeded_random__ruckig_min_08_checked (by decide +kernel)

theorem biased_alternation__ruckig_certificate : PositionCertificate biased_alternation__ruckig :=
  certificate_of_check biased_alternation__ruckig_checked (by decide +kernel)

theorem biased_alternation__ruckig_min_08_certificate : PositionCertificate biased_alternation__ruckig_min_08 :=
  certificate_of_check biased_alternation__ruckig_min_08_checked (by decide +kernel)

end NativeRational
