module
public import JointFilter
@[expose] public section
noncomputable section
namespace LeanControls.FiniteJointFilter
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking JointFilter

/-- Dynamics and pointwise input bounds for one actual constant-jerk segment.
There is no tracking, filter-error, or command-rate bound in this structure. -/
structure Segment (σ W J l H j : ℝ) (f q : ℝ → State) (r w u : ℝ → ℝ) : Prop where
  duration : 0 ≤ H
  plant : IsTrajectory H r (fun t => u t+w t) f
  reference_continuous : ContinuousOn q (Icc 0 H)
  reference_ode : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
    HasDerivAt (fun s => q s i) (![q t 1,q t 2,j] i) t
  filter_continuous : ContinuousOn u (Icc 0 H)
  filter_ode : ∀ t ∈ Ioo 0 H,
    HasDerivAt u (l*(physicalInput σ f q (fun _ => j) t-u t)) t
  rate_lower : ∀ t ∈ Icc 0 H, 8*σ ≤ r t
  rate_upper : ∀ t ∈ Icc 0 H, r t ≤ 12*σ
  disturbance : ∀ t ∈ Icc 0 H, |w t| ≤ W
  jerk : |j| ≤ J

def JointBox (σ R D j : ℝ) (f q : ℝ → State) (u : ℝ → ℝ) (t : ℝ) : Prop :=
  (∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R) ∧
  |u t-physicalInput σ f q (fun _ => j) t| ≤ D

theorem segment {σ R D W J l H j : ℝ} {f q : ℝ → State} {r w u : ℝ → ℝ}
    (hσ : 0 < σ) (hR : 0 < R) (hD : 0 < D) (hW : 0 ≤ W) (hJ : 0 ≤ J)
    (b1 : W+D+J/(48*σ) ≤ 2*σ^2*R)
    (b2 : 96*σ^3*R+(13/12)*J+6*σ*W ≤ (l-6*σ)*D)
    (hs : Segment σ W J l H j f q r w u)
    (hi : JointBox σ R D j f q u 0) :
    ∀ t ∈ Icc 0 H, JointBox σ R D j f q u t :=
  actual_joint_scaled hσ hs.duration hR hD hW hJ hs.plant hs.reference_continuous
    hs.reference_ode hs.filter_continuous hs.filter_ode hs.rate_lower hs.rate_upper
    hs.disturbance hs.jerk b1 b2 hi.1 hi.2

/-- The physical and reference states match. The filter retains its old value.
Admission uses the exact post-jump mismatch, without resetting the filter. -/
theorem matched_handoff {σ R D h jOld jNew : ℝ}
    {f g q p : ℝ → State} {u v : ℝ → ℝ}
    (hf : g 0 = f h) (hq : p 0 = q h) (hu : v 0 = u h)
    (hold : JointBox σ R D jOld f q u h)
    (admit : |(u h-physicalInput σ f q (fun _ => jOld) h)-
      (5/(48*σ))*(jNew-jOld)| ≤ D) :
    JointBox σ R D jNew g p v 0 := by
  constructor
  · intro i
    change |coordinates 0 (scaleState σ (error g p 0)) i| ≤ R
    rw [matched_error hf hq]
    exact hold.1 i
  · change |v 0-physicalInput σ g p (fun _ => jNew) 0| ≤ D
    rw [hu,CommandSmoothing.matched_mismatch_transfer σ h jOld jNew (u h) hf hq]
    exact admit

/-- Finite composition of actual segments with retained filter state. Each
accepted switch satisfies the exact state-dependent mismatch test. -/
theorem finite_segments {N : ℕ} {σ R D W J l : ℝ}
    (hσ : 0 < σ) (hR : 0 < R) (hD : 0 < D) (hW : 0 ≤ W) (hJ : 0 ≤ J)
    (b1 : W+D+J/(48*σ) ≤ 2*σ^2*R)
    (b2 : 96*σ^3*R+(13/12)*J+6*σ*W ≤ (l-6*σ)*D)
    {H j : ℕ → ℝ} {f q : ℕ → ℝ → State} {r w u : ℕ → ℝ → ℝ}
    (hs : ∀ k < N, Segment σ W J l (H k) (j k) (f k) (q k) (r k) (w k) (u k))
    (hf : ∀ k, k+1 < N → f (k+1) 0 = f k (H k))
    (hq : ∀ k, k+1 < N → q (k+1) 0 = q k (H k))
    (hu : ∀ k, k+1 < N → u (k+1) 0 = u k (H k))
    (admit : ∀ k, k+1 < N →
      |(u k (H k)-physicalInput σ (f k) (q k) (fun _ => j k) (H k))-
        (5/(48*σ))*(j (k+1)-j k)| ≤ D)
    (hi : JointBox σ R D (j 0) (f 0) (q 0) (u 0) 0) :
    ∀ k < N, ∀ t ∈ Icc 0 (H k), JointBox σ R D (j k) (f k) (q k) (u k) t := by
  have start : ∀ k, k < N → JointBox σ R D (j k) (f k) (q k) (u k) 0 := by
    intro k
    induction k with
    | zero => exact fun _ => hi
    | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      have hend := segment hσ hR hD hW hJ b1 b2 (hs k hk') (ih hk') (H k)
        ⟨(hs k hk').duration,le_rfl⟩
      exact matched_handoff (hf k hk) (hq k hk) (hu k hk) hend (admit k hk)
  exact fun k hk => segment hσ hR hD hW hJ b1 b2 (hs k hk) (start k hk)

-- This is an admission arithmetic witness, not existence of a specific motion.
theorem nonzero_admitted_update :
    |(0:ℝ)-(5/(48*10))*(1/2-0)| ≤ 11/1200 ∧ (0:ℝ) < |1/2| := by
  constructor <;> norm_num

theorem large_jump_still_rejected :
    ¬ ∃ d : ℝ, |d| ≤ 11/1200 ∧ |d-5/24| ≤ 11/1200 :=
  CommandSmoothing.illustrative_jump_incompatible

/-- These sufficient budgets require a fast filter. This is a limitation of
this certificate and does not imply a smoothing or hardware benefit. -/
theorem necessary_filter_rate {σ R D W J l : ℝ}
    (hσ : 0 < σ) (hD : 0 < D) (hW : 0 ≤ W) (hJ : 0 ≤ J)
    (b1 : W+D+J/(48*σ) ≤ 2*σ^2*R)
    (b2 : 96*σ^3*R+(13/12)*J+6*σ*W ≤ (l-6*σ)*D) :
    54*σ ≤ l := by
  have hJterm : 0 ≤ J/(48*σ) := div_nonneg hJ (by positivity)
  have hd : D ≤ 2*σ^2*R := by linarith
  have hp := mul_le_mul_of_nonneg_left hd (show 0 ≤ 48*σ by positivity)
  have hwterm := mul_nonneg hσ.le hW
  nlinarith

end LeanControls.FiniteJointFilter
