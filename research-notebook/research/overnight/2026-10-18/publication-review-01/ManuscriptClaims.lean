import PhysicalArrival
import HistoryPruning
import SuccessorGuard

open Set
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

namespace PublicationReview

/-- The paper's three physical error bounds follow from its stated invariant cube.
Reference continuity and the three derivative identities are explicit. -/
theorem manuscript_tracking_bounds {σ H R W J : ℝ}
    (hσ : 0 < σ) (hH : 0 ≤ H) (hR : 0 ≤ R)
    {r w j : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => physicalInput σ f q j t + w t) f)
    (hq : ContinuousOn q (Icc 0 H))
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1, q t 2, j t] i) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8*σ ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12*σ)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (hj : ∀ t ∈ Icc 0 H, |j t| ≤ J)
    (budget : W+J/(48*σ) ≤ 2*σ^2*R)
    (hi : ∀ i, |coordinates 0 (scaledError σ f q 0) i| ≤ R) :
    ∀ t ∈ Icc 0 H,
      |f t 0-q t 0| ≤ R ∧
      |f t 1-q t 1| ≤ 8*σ*R ∧
      |f t 2-q t 2| ≤ 64*σ^2*R := by
  intro t ht
  have cube := tracking_cube_scaled hσ hH hR hf hq hdq hrlo hrhi hw hj budget hi t ht
  have physical := scaled_cube_physical_bounds hσ cube
  exact ⟨physical.1,physical.2.1,physical.2.2.1⟩

/-- The declared initial cube does not impose the reference's acceleration cap
on the physical state. This is a pointwise initial-condition witness only. -/
theorem initial_cube_allows_acceleration_above_reference_limit :
    (∀ i, |coordinates 0 (scaleState 10 (![1/5000,-2/125,32/25] : State)) i| ≤ 1/5000) ∧
    (1/2:ℝ) < (32/25:ℝ) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [coordinates,scaleState]
  · norm_num

/-- A point in the proved position band need not be at the exact target. -/
theorem position_band_is_not_exact_rest :
    |(1/10000:ℝ)| ≤ 1/5000 ∧ (1/10000:ℝ) ≠ 0 := by norm_num

#print axioms PublicationReview.manuscript_tracking_bounds
#print axioms PublicationReview.initial_cube_allows_acceleration_above_reference_limit
#print axioms PublicationReview.position_band_is_not_exact_rest
end PublicationReview
