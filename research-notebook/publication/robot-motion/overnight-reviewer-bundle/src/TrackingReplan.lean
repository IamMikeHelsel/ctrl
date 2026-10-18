module
public import RobustHold
public import SmoothReplan
@[expose] public section
noncomputable section
namespace LeanControls.TrackingReplan
open Set
open UncertainLag (State)
open VariableResponse RobustHold

/-- Physical tracking error relative to a planned position, velocity and acceleration. -/
def error (f q : ℝ → State) (t : ℝ) : State := fun i => f t i - q t i

/-- Acceleration feedforward, fixed error feedback, and planned jerk feedforward. -/
def input (κ : ℝ) (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) : ℝ :=
  q t 2 + command 0 (error f q t) + κ * j t

def residual (κ : ℝ) (r w j : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t + (κ - 1 / r t) * j t

/-- The error dynamics are derived from the actual plant. Derivatives are only
required inside a segment. They need not exist at a replan boundary. -/
theorem error_trajectory {H κ : ℝ} {r w j : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => input κ f q j t + w t) f)
    (hq : ContinuousOn q (Icc 0 H))
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1, q t 2, j t] i) t)
    (hr : ∀ t ∈ Ioo 0 H, r t ≠ 0) :
    IsTrajectory H r (fun t => command 0 (error f q t) + residual κ r w j t)
      (error f q) := by
  constructor
  · exact hf.continuous.sub hq
  · intro t ht i
    have he := (hf.ode t ht i).sub (hdq t ht i)
    change HasDerivAt (fun s => f s i - q s i) _ t
    convert he using 1
    fin_cases i <;> simp [error, input, residual]
    field_simp [hr t ht]
    ring

/-- Reciprocal rate uncertainty for the checked band. -/
theorem reciprocal_band {r : ℝ} (hlo : 8 ≤ r) (hhi : r ≤ 12) :
    (1:ℝ)/12 ≤ 1/r ∧ 1/r ≤ 1/8 := by
  have hr : 0 < r := by linarith
  constructor
  · apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<12) hr).mpr
    linarith
  · apply (div_le_div_iff₀ hr (by norm_num : (0:ℝ)<8)).mpr
    linarith

theorem centered_reciprocal_bound {r : ℝ} (hlo : 8 ≤ r) (hhi : r ≤ 12) :
    |(5:ℝ)/48 - 1/r| ≤ 1/48 := by
  obtain ⟨hl,hu⟩ := reciprocal_band hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- This minimizes the worst endpoint residual in this certificate, not every
finite-time tracking metric. -/
theorem reciprocal_minimax (κ : ℝ) :
    (1:ℝ)/48 ≤ max |κ-1/8| |κ-1/12| := by
  have ha := (abs_le.mp (le_max_left |κ-1/8| |κ-1/12|)).1
  have hb := (abs_le.mp (le_max_right |κ-1/8| |κ-1/12|)).2
  linarith

theorem residual_bound {κ r w j B W J : ℝ}
    (hB : 0 ≤ B) (hκ : |κ-1/r| ≤ B) (hw : |w| ≤ W) (hj : |j| ≤ J) :
    |w+(κ-1/r)*j| ≤ W+B*J := by
  calc
    _ ≤ |w| + |(κ-1/r)*j| := abs_add_le _ _
    _ = |w| + |κ-1/r| *|j| := by rw [abs_mul]
    _ ≤ W+B*J := add_le_add hw (mul_le_mul hκ hj (abs_nonneg _) hB)

/-- Actual error stays in the inherited invariant cube for an entire segment. -/
theorem tracking_cube {H R κ B W J : ℝ}
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hB : 0 ≤ B)
    {r w j : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => input κ f q j t + w t) f)
    (hq : ContinuousOn q (Icc 0 H))
    (hdq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1, q t 2, j t] i) t)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hκ : ∀ t ∈ Icc 0 H, |κ-1/r t| ≤ B)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W) (hj : ∀ t ∈ Icc 0 H, |j t| ≤ J)
    (budget : W+B*J ≤ 2*R)
    (hi : ∀ i, |coordinates 0 (error f q 0) i| ≤ R) :
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates 0 (error f q t) i| ≤ R := by
  apply actual_hold_invariant hH hR
    (error_trajectory hf hq hdq (fun t ht => ne_of_gt (by linarith [hrlo t ⟨ht.1.le,ht.2.le⟩])))
    hrlo hrhi
  · intro t ht
    exact (residual_bound hB (hκ t ht) (hw t ht) (hj t ht)).trans budget
  · exact hi

/-- Convert the error cube to physical margins. The reference limits and the
actual limits differ by the stated error bounds. -/
theorem physical_margins {R L U V A κ J W : ℝ} {f q : ℝ → State} {j w : ℝ → ℝ} {t : ℝ}
    (hz : ∀ i, |coordinates 0 (error f q t) i| ≤ R)
    (hq : q t 0 ∈ Icc (L+R) (U-R))
    (hv : |q t 1| ≤ V) (ha : |q t 2| ≤ A)
    (hj : |j t| ≤ J) (hw : |w t| ≤ W) :
    f t 0 ∈ Icc L U ∧ |f t 1| ≤ V+8*R ∧ |f t 2| ≤ A+64*R ∧
      |input κ f q j t + w t| ≤ A+24*R+|κ| *J+W := by
  obtain ⟨hx,hev,hea,hc⟩ := cube_physical_bounds hz
  have ex : |f t 0-q t 0| ≤ R := by simpa [error] using hx
  have ev : |f t 1-q t 1| ≤ 8*R := hev
  have ea : |f t 2-q t 2| ≤ 64*R := hea
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · linarith [(abs_le.mp ex).1,hq.1]
  · linarith [(abs_le.mp ex).2,hq.2]
  · calc |f t 1| = |q t 1+(f t 1-q t 1)| := by congr 1; ring
         _ ≤ |q t 1|+|f t 1-q t 1| := abs_add_le _ _
         _ ≤ V+8*R := add_le_add hv ev
  · calc |f t 2| = |q t 2+(f t 2-q t 2)| := by congr 1; ring
         _ ≤ |q t 2|+|f t 2-q t 2| := abs_add_le _ _
         _ ≤ A+64*R := add_le_add ha ea
  · have hm : |κ*j t| ≤ |κ| *J := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hj (abs_nonneg _)
    unfold input
    calc
      _ ≤ |q t 2+command 0 (error f q t)+κ*j t|+|w t| := abs_add_le _ _
      _ ≤ (|q t 2+command 0 (error f q t)|+|κ*j t|)+W := add_le_add (abs_add_le _ _) hw
      _ ≤ ((|q t 2|+|command 0 (error f q t)|)+|κ| *J)+W := by gcongr; exact abs_add_le _ _
      _ ≤ A+24*R+|κ| *J+W := by gcongr

/-- A constant-jerk reference in the same state representation as the plant. -/
def reference (z : SmoothReplan.State) (j t : ℝ) : State :=
  ![SmoothReplan.position z j t, SmoothReplan.velocity z j t, SmoothReplan.acceleration z j t]

theorem reference_derivative (z : SmoothReplan.State) (j t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => reference z j s i)
      (![reference z j t 1, reference z j t 2, j] i) t := by
  fin_cases i
  · simpa [reference] using SmoothReplan.segment_position_derivative z j t
  · simpa [reference] using SmoothReplan.segment_velocity_derivative z j t
  · simpa [reference] using SmoothReplan.segment_acceleration_derivative z j t

theorem reference_continuous (z : SmoothReplan.State) (j : ℝ) :
    Continuous (reference z j) := by
  apply continuous_pi
  intro i
  exact continuous_iff_continuousAt.mpr (fun t => (reference_derivative z j t i).continuousAt)

theorem reference_matched (z : SmoothReplan.State) (jOld jNew h : ℝ) :
    reference (SmoothReplan.advance z jOld h) jNew 0 = reference z jOld h := by
  ext i
  fin_cases i <;> simp [reference, SmoothReplan.advance, SmoothReplan.position,
    SmoothReplan.velocity, SmoothReplan.acceleration]

/-- A matched physical state and matched reference preserve the same error cube. -/
theorem matched_error {f g q p : ℝ → State} {h : ℝ}
    (hf : g 0 = f h) (hq : p 0 = q h) : error g p 0 = error f q h := by
  unfold error
  rw [hf, hq]

/-- Finite segment induction. Every segment has its own open-interior ODE.
There is no derivative assertion across switches, and no infinite/Zeno claim. -/
theorem finite_replans {N : ℕ} {R : ℝ}
    {duration : ℕ → ℝ} {f q : ℕ → ℝ → State}
    (hduration : ∀ k < N, 0 ≤ duration k)
    (hsegment : ∀ k < N, (∀ i, |coordinates 0 (error (f k) (q k) 0) i| ≤ R) →
      ∀ t ∈ Icc 0 (duration k), ∀ i, |coordinates 0 (error (f k) (q k) t) i| ≤ R)
    (hphysical : ∀ k, k+1 < N → f (k+1) 0 = f k (duration k))
    (hreference : ∀ k, k+1 < N → q (k+1) 0 = q k (duration k))
    (hi : ∀ i, |coordinates 0 (error (f 0) (q 0) 0) i| ≤ R) :
    ∀ k < N, ∀ t ∈ Icc 0 (duration k), ∀ i,
      |coordinates 0 (error (f k) (q k) t) i| ≤ R := by
  have hstart : ∀ k, k < N → ∀ i, |coordinates 0 (error (f k) (q k) 0) i| ≤ R := by
    intro k
    induction k with
    | zero => exact fun _ => hi
    | succ k ih =>
      intro hk i
      rw [matched_error (hphysical k hk) (hreference k hk)]
      exact hsegment k (by omega) (ih (by omega)) (duration k)
        ⟨hduration k (by omega),le_rfl⟩ i
  exact fun k hk => hsegment k hk (hstart k hk)


/-- The selected jerk feedforward gives a complete admitted-segment certificate
for the actual axis. Reference bounds leave room for the tracking error. -/
theorem admitted_tracking_segment {H R W J L U V A : ℝ}
    (hR : 0 ≤ R) {z : SmoothReplan.State} {j : ℝ}
    (hc : SmoothReplan.Admission z j H (L+R) (U-R) V A J)
    {r w : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r
      (fun t => input (5/48) f (reference z j) (fun _ => j) t + w t) f)
    (hrlo : ∀ t ∈ Icc 0 H, 8 ≤ r t) (hrhi : ∀ t ∈ Icc 0 H, r t ≤ 12)
    (hw : ∀ t ∈ Icc 0 H, |w t| ≤ W)
    (budget : W+J/48 ≤ 2*R)
    (hi : ∀ i, |coordinates 0 (error f (reference z j) 0) i| ≤ R) :
    ∀ t ∈ Icc 0 H,
      (∀ i, |coordinates 0 (error f (reference z j) t) i| ≤ R) ∧
      f t 0 ∈ Icc L U ∧ |f t 1| ≤ V+8*R ∧ |f t 2| ≤ A+64*R ∧
      |input (5/48) f (reference z j) (fun _ => j) t+w t| ≤ A+24*R+5*J/48+W := by
  have hcub := tracking_cube hc.duration.le hR (by norm_num : (0:ℝ) ≤ 1/48)
    hf (reference_continuous z j).continuousOn (fun t _ i => reference_derivative z j t i)
    hrlo hrhi (fun t ht => centered_reciprocal_bound (hrlo t ht) (hrhi t ht))
    hw (fun _ _ => hc.jerk) (by linarith) hi
  intro t ht
  obtain ⟨hq,hv,ha,hj⟩ := SmoothReplan.admission_all_time hc ht
  have hp := physical_margins (κ := (5:ℝ)/48) (j := fun _ => j) (w := w) (hcub t ht) hq
    (abs_le.mpr hv) (abs_le.mpr ha) hj (hw t ht)
  refine ⟨hcub t ht,hp.1,hp.2.1,hp.2.2.1,?_⟩
  convert hp.2.2.2 using 1
  norm_num
  ring

/-- Physical tracking across any finite matched sequence. The dynamics, rate
band and disturbance budget are checked on each segment. No dwell-time lower
bound is used. The result is conditional on the stated physical trajectories. -/
theorem actual_finite_replans {N : ℕ} {R W J : ℝ}
    (hR : 0 ≤ R) {duration : ℕ → ℝ} {f q : ℕ → ℝ → State}
    {r w j : ℕ → ℝ → ℝ}
    (hduration : ∀ k < N, 0 ≤ duration k)
    (hf : ∀ k < N, IsTrajectory (duration k) (r k)
      (fun t => input (5/48) (f k) (q k) (j k) t + w k t) (f k))
    (hq : ∀ k < N, ContinuousOn (q k) (Icc 0 (duration k)))
    (hdq : ∀ k < N, ∀ t ∈ Ioo 0 (duration k), ∀ i : Fin 3,
      HasDerivAt (fun s => q k s i) (![q k t 1,q k t 2,j k t] i) t)
    (hrlo : ∀ k < N, ∀ t ∈ Icc 0 (duration k), 8 ≤ r k t)
    (hrhi : ∀ k < N, ∀ t ∈ Icc 0 (duration k), r k t ≤ 12)
    (hw : ∀ k < N, ∀ t ∈ Icc 0 (duration k), |w k t| ≤ W)
    (hj : ∀ k < N, ∀ t ∈ Icc 0 (duration k), |j k t| ≤ J)
    (budget : W+J/48 ≤ 2*R)
    (hphysical : ∀ k, k+1 < N → f (k+1) 0 = f k (duration k))
    (hreference : ∀ k, k+1 < N → q (k+1) 0 = q k (duration k))
    (hi : ∀ i, |coordinates 0 (error (f 0) (q 0) 0) i| ≤ R) :
    ∀ k < N, ∀ t ∈ Icc 0 (duration k), ∀ i,
      |coordinates 0 (error (f k) (q k) t) i| ≤ R := by
  apply finite_replans hduration _ hphysical hreference hi
  intro k hk hstart
  exact tracking_cube (hduration k hk) hR (by norm_num : (0:ℝ) ≤ 1/48)
    (hf k hk) (hq k hk) (hdq k hk) (hrlo k hk) (hrhi k hk)
    (fun t ht => centered_reciprocal_bound (hrlo k hk t ht) (hrhi k hk t ht))
    (hw k hk) (hj k hk) (by linarith) hstart

/-- Nominal inverse lag has a slightly larger cube residual bound. -/
theorem nominal_reciprocal_bound {r : ℝ} (hlo : 8 ≤ r) (hhi : r ≤ 12) :
    |(1:ℝ)/10-1/r| ≤ 1/40 := by
  obtain ⟨hl,hu⟩ := reciprocal_band hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The short-time derivative criterion has a different minimax coefficient. -/
theorem instantaneous_minimax (κ : ℝ) :
    (1:ℝ)/5 ≤ max |8*κ-1| |12*κ-1| := by
  have ha := (abs_le.mp (le_max_left |8*κ-1| |12*κ-1|)).1
  have hb := (abs_le.mp (le_max_right |8*κ-1| |12*κ-1|)).2
  linarith

theorem instantaneous_nominal_bound {r : ℝ} (hlo : 8 ≤ r) (hhi : r ≤ 12) :
    |r/10-1| ≤ 1/5 := by
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A planned jerk bound is not the same as a plant jerk bound. -/
theorem actual_jerk_rhs_can_exceed_reference : (12:ℝ)*(5/48)*1 > 1 := by norm_num


/-- A tighter bound on the feedback part of actual jerk than separate bounds
on command and acceleration would give. -/
theorem cube_drive_bound {R : ℝ} {s : State}
    (hz : ∀ i, |coordinates 0 s i| ≤ R) : |command 0 s-s 2| ≤ 56*R := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have h2 := abs_le.mp (hz 2)
  simp [coordinates] at h0 h1 h2
  apply abs_le.mpr
  simp [command]
  constructor <;> linarith

/-- Actual acceleration has this derivative bound inside each segment.
The bound is generally larger than the planned jerk bound J. -/
theorem actual_jerk_bound {H R κ W J t : ℝ}
    {r w j : ℝ → ℝ} {f q : ℝ → State}
    (hf : IsTrajectory H r (fun t => input κ f q j t + w t) f)
    (ht : t ∈ Ioo 0 H) (hr : |r t| ≤ 12)
    (hz : ∀ i, |coordinates 0 (error f q t) i| ≤ R)
    (hw : |w t| ≤ W) (hj : |j t| ≤ J) :
    ∃ d, HasDerivAt (fun s => f s 2) d t ∧ |d| ≤ 12*(56*R+|κ| * J+W) := by
  refine ⟨r t*(input κ f q j t+w t-f t 2),?_,?_⟩
  · simpa using hf.ode t ht 2
  · have hc := cube_drive_bound hz
    have heq : input κ f q j t+w t-f t 2 =
        (command 0 (error f q t)-error f q t 2)+κ*j t+w t := by
      unfold input error
      ring
    rw [abs_mul,heq]
    have hb : |(command 0 (error f q t)-error f q t 2)+κ*j t+w t| ≤
        56*R+|κ| * J+W := by
      calc
        _ ≤ |(command 0 (error f q t)-error f q t 2)+κ*j t|+|w t| := abs_add_le _ _
        _ ≤ (|command 0 (error f q t)-error f q t 2|+|κ*j t|)+W :=
          add_le_add (abs_add_le _ _) hw
        _ ≤ 56*R+|κ| * J+W := by
          rw [abs_mul]
          gcongr
    exact mul_le_mul hr hb (abs_nonneg _) (by norm_num)

end LeanControls.TrackingReplan
