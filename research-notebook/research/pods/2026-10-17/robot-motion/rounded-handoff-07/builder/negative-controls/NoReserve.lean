module
public import ScaledTracking
@[expose] public section
noncomputable section
namespace LeanControls.RoundedHandoff
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan ScaledTracking

/-- Initial radius plus all reference-jump reserves before this piece. -/
def radius (R₀ : ℝ) (B : ℕ → ℝ) (k : ℕ) : ℝ :=
  R₀ + (Finset.range k).sum B

@[simp] theorem radius_zero (R₀ : ℝ) (B : ℕ → ℝ) : radius R₀ B 0 = R₀ := by
  simp [radius]

theorem radius_succ (R₀ : ℝ) (B : ℕ → ℝ) (k : ℕ) :
    radius R₀ B (k+1) = radius R₀ B k + B k := by
  simp [radius, Finset.sum_range_succ, add_assoc]

theorem radius_ge_initial (R₀ : ℝ) {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k) (k : ℕ) :
    R₀ ≤ radius R₀ B k := by
  have hs : 0 ≤ (Finset.range k).sum B := Finset.sum_nonneg (fun l _ => hB l)
  dsimp [radius]
  linarith

theorem radius_nonneg {R₀ : ℝ} (hR : 0 ≤ R₀) {B : ℕ → ℝ}
    (hB : ∀ k, 0 ≤ B k) (k : ℕ) : 0 ≤ radius R₀ B k :=
  hR.trans (radius_ge_initial R₀ hB k)

/-- The scale and centered coordinate map are linear, including at sigma=0. -/
theorem transformed_sub (σ : ℝ) (s t : State) :
    coordinates 0 (scaleState σ (s-t)) =
      coordinates 0 (scaleState σ s) - coordinates 0 (scaleState σ t) := by
  ext i
  fin_cases i <;> simp [coordinates, scaleState, sub_div] <;> ring

/-- Physical state matches. A reference jump subtracts from the error. -/
theorem handoff_coordinates (σ : ℝ) {f g q p : ℝ → State} {h : ℝ}
    (hphysical : g 0 = f h) (i : Fin 3) :
    coordinates 0 (scaledError σ g p 0) i =
      coordinates 0 (scaledError σ f q h) i -
        coordinates 0 (scaleState σ (p 0-q h)) i := by
  have he : error g p 0 = error f q h - (p 0-q h) := by
    ext k
    simp [error, hphysical]
  change coordinates 0 (scaleState σ (error g p 0)) i =
    coordinates 0 (scaleState σ (error f q h)) i -
      coordinates 0 (scaleState σ (p 0-q h)) i
  rw [he, transformed_sub]
  rfl

/-- A jump reserve bounds the new error cube without requiring a matched reference. -/
theorem handoff_radius {σ R B : ℝ} {f g q p : ℝ → State} {h : ℝ}
    (hphysical : g 0 = f h)
    (hold : ∀ i, |coordinates 0 (scaledError σ f q h) i| ≤ R)
    (hjump : ∀ i, |coordinates 0 (scaleState σ (p 0-q h)) i| ≤ B) :
    ∀ i, |coordinates 0 (scaledError σ g p 0) i| ≤ R := by
  intro i
  rw [handoff_coordinates σ hphysical i]
  exact (abs_sub _ _).trans (add_le_add (hold i) (hjump i))

theorem budget_at_radius {σ R₀ W J : ℝ} {B : ℕ → ℝ}
    (hB : ∀ k, 0 ≤ B k)
    (budget : W+J/(48*σ) ≤ 2*σ^2*R₀) (k : ℕ) :
    W+J/(48*σ) ≤ 2*σ^2*radius R₀ B k := by
  exact budget.trans (mul_le_mul_of_nonneg_left (radius_ge_initial R₀ hB k)
    (by positivity : 0 ≤ 2*σ^2))

/-- Finite tracking for actual physical trajectories with nonzero reference joins.
All differential equations are local to piece interiors; no switch derivative is used. -/
theorem finite_replans_with_jumps_scaled {N : ℕ} {σ R₀ W J : ℝ}
    (hσ : 0 < σ) (hR : 0 ≤ R₀) {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k)
    {duration : ℕ → ℝ} {f q : ℕ → ℝ → State} {r w j : ℕ → ℝ → ℝ}
    (hduration : ∀ k < N, 0 ≤ duration k)
    (hf : ∀ k < N, IsTrajectory (duration k) (r k)
      (fun t => physicalInput σ (f k) (q k) (j k) t + w k t) (f k))
    (hq : ∀ k < N, ContinuousOn (q k) (Icc 0 (duration k)))
    (hdq : ∀ k < N, ∀ t ∈ Ioo 0 (duration k), ∀ i : Fin 3,
      HasDerivAt (fun s => q k s i) (![q k t 1,q k t 2,j k t] i) t)
    (hrlo : ∀ k < N, ∀ t ∈ Icc 0 (duration k), 8*σ ≤ r k t)
    (hrhi : ∀ k < N, ∀ t ∈ Icc 0 (duration k), r k t ≤ 12*σ)
    (hw : ∀ k < N, ∀ t ∈ Icc 0 (duration k), |w k t| ≤ W)
    (hj : ∀ k < N, ∀ t ∈ Icc 0 (duration k), |j k t| ≤ J)
    (budget : W+J/(48*σ) ≤ 2*σ^2*R₀)
    (hphysical : ∀ k, k+1 < N → f (k+1) 0 = f k (duration k))
    (hjump : ∀ k, k+1 < N → ∀ i,
      |coordinates 0 (scaleState σ (q (k+1) 0-q k (duration k))) i| ≤ B k)
    (hi : ∀ i, |coordinates 0 (scaledError σ (f 0) (q 0) 0) i| ≤ R₀) :
    ∀ k < N, ∀ t ∈ Icc 0 (duration k), ∀ i,
      |coordinates 0 (scaledError σ (f k) (q k) t) i| ≤ radius R₀ B k := by
  have hsegment : ∀ k < N,
      (∀ i, |coordinates 0 (scaledError σ (f k) (q k) 0) i| ≤ radius R₀ B k) →
      ∀ t ∈ Icc 0 (duration k), ∀ i,
        |coordinates 0 (scaledError σ (f k) (q k) t) i| ≤ radius R₀ B k := by
    intro k hk hstart
    exact tracking_cube_scaled hσ (hduration k hk) (radius_nonneg hR hB k)
      (hf k hk) (hq k hk) (hdq k hk) (hrlo k hk) (hrhi k hk)
      (hw k hk) (hj k hk) (budget_at_radius hB budget k) hstart
  have hstart : ∀ k, k < N → ∀ i,
      |coordinates 0 (scaledError σ (f k) (q k) 0) i| ≤ radius R₀ B k := by
    intro k
    induction k with
    | zero => simpa only [radius_zero] using (fun _ : 0 < N => hi)
    | succ k ih =>
      intro hk
      have hend := hsegment k (by omega) (ih (by omega)) (duration k)
        ⟨hduration k (by omega),le_rfl⟩
      simpa only [radius_succ] using handoff_radius (hphysical k hk) hend (hjump k hk)
  exact fun k hk => hsegment k hk (hstart k hk)

/-- Physical error bounds from a jump-inflated transformed cube. -/
theorem tracking_error_bounds {σ R : ℝ} (hσ : 0 < σ)
    {f q : ℝ → State} {t : ℝ}
    (hz : ∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R) :
    |f t 0-q t 0| ≤ R ∧ |f t 1-q t 1| ≤ 8*σ*R ∧
      |f t 2-q t 2| ≤ 64*σ^2*R := by
  obtain ⟨hx,hv,ha,_⟩ := scaled_cube_physical_bounds hσ hz
  exact ⟨hx,hv,ha⟩

/-- Bounds on actual position, velocity and acceleration, not only error coordinates. -/
theorem actual_state_bounds {σ R P V A : ℝ} (hσ : 0 < σ)
    {f q : ℝ → State} {t : ℝ}
    (hz : ∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R)
    (hp : |q t 0| ≤ P) (hv : |q t 1| ≤ V) (ha : |q t 2| ≤ A) :
    |f t 0| ≤ P+R ∧ |f t 1| ≤ V+8*σ*R ∧ |f t 2| ≤ A+64*σ^2*R := by
  obtain ⟨he0,he1,he2⟩ := tracking_error_bounds hσ hz
  have bound (a b K E : ℝ) (hb : |b| ≤ K) (he : |a-b| ≤ E) : |a| ≤ K+E := by
    calc |a| = |b+(a-b)| := by congr 1; ring
         _ ≤ |b|+|a-b| := abs_add_le _ _
         _ ≤ K+E := add_le_add hb he
  exact ⟨bound _ _ _ _ hp he0,bound _ _ _ _ hv he1,bound _ _ _ _ ha he2⟩

/-- Arbitrary cubic coefficients use the already proved local derivative chain.
The actual plant trajectory and physical handoffs remain explicit premises. -/
theorem finite_cubic_replans {N : ℕ} {σ R₀ W J : ℝ}
    (hσ : 0 < σ) (hR : 0 ≤ R₀) {B : ℕ → ℝ} (hB : ∀ k, 0 ≤ B k)
    {duration : ℕ → ℝ} {f : ℕ → ℝ → State} {r w : ℕ → ℝ → ℝ}
    {z : ℕ → SmoothReplan.State} {jerk : ℕ → ℝ}
    (hduration : ∀ k < N, 0 ≤ duration k)
    (hf : ∀ k < N, IsTrajectory (duration k) (r k)
      (fun t => physicalInput σ (f k) (reference (z k) (jerk k))
        (fun _ => jerk k) t + w k t) (f k))
    (hrlo : ∀ k < N, ∀ t ∈ Icc 0 (duration k), 8*σ ≤ r k t)
    (hrhi : ∀ k < N, ∀ t ∈ Icc 0 (duration k), r k t ≤ 12*σ)
    (hw : ∀ k < N, ∀ t ∈ Icc 0 (duration k), |w k t| ≤ W)
    (hj : ∀ k < N, |jerk k| ≤ J)
    (budget : W+J/(48*σ) ≤ 2*σ^2*R₀)
    (hphysical : ∀ k, k+1 < N → f (k+1) 0 = f k (duration k))
    (hjump : ∀ k, k+1 < N → ∀ i,
      |coordinates 0 (scaleState σ
        (reference (z (k+1)) (jerk (k+1)) 0 -
          reference (z k) (jerk k) (duration k))) i| ≤ B k)
    (hi : ∀ i, |coordinates 0 (scaledError σ (f 0)
      (reference (z 0) (jerk 0)) 0) i| ≤ R₀) :
    ∀ k < N, ∀ t ∈ Icc 0 (duration k), ∀ i,
      |coordinates 0 (scaledError σ (f k) (reference (z k) (jerk k)) t) i| ≤
        radius R₀ B k := by
  exact finite_replans_with_jumps_scaled hσ hR hB hduration hf
    (fun k _ => (reference_continuous (z k) (jerk k)).continuousOn)
    (fun k _ t _ i => reference_derivative (z k) (jerk k) t i)
    hrlo hrhi hw (fun k hk _ _ => hj k hk) budget hphysical hjump hi

/-- A constant reserve makes the accumulated bound explicit. -/
theorem constant_radius (R₀ B : ℝ) (k : ℕ) :
    radius R₀ (fun _ => B) k = R₀ + k*B := by
  simp [radius]

/-- With zero reference reserve, the generalized radius recovers the old radius. -/
@[simp] theorem zero_reserve_radius (R₀ : ℝ) (k : ℕ) :
    radius R₀ (fun _ => 0) k = R₀ := by
  simp [radius]

end LeanControls.RoundedHandoff
