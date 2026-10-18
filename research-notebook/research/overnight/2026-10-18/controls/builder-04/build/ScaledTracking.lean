module
public import TrackingReplan
@[expose] public section
noncomputable section
namespace LeanControls.ScaledTracking
open Set
open UncertainLag (State)
open VariableResponse RobustHold TrackingReplan

/-- Position is unchanged. Velocity and acceleration use the new time unit. -/
def scaleState (σ : ℝ) (s : State) : State := fun i => s i / σ ^ i.val

def normalize (σ : ℝ) (f : ℝ → State) (τ : ℝ) : State :=
  scaleState σ (f (τ / σ))

def scaledError (σ : ℝ) (f q : ℝ → State) (t : ℝ) : State :=
  scaleState σ (error f q t)

/-- The physical controller. The reference's third component is acceleration. -/
def physicalInput (σ : ℝ) (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) : ℝ :=
  q t 2 - 8 * σ^2 * (f t 0 - q t 0) - 6 * σ * (f t 1 - q t 1) -
    (f t 2 - q t 2) / 2 + (5 / (48 * σ)) * j t

lemma div_mem_Icc {σ H τ : ℝ} (hσ : 0 < σ) (hτ : τ ∈ Icc 0 (σ * H)) :
    τ / σ ∈ Icc 0 H := by
  constructor
  · exact div_nonneg hτ.1 hσ.le
  · exact (div_le_iff₀ hσ).2 (by nlinarith [hτ.2])

lemma div_mem_Ioo {σ H τ : ℝ} (hσ : 0 < σ) (hτ : τ ∈ Ioo 0 (σ * H)) :
    τ / σ ∈ Ioo 0 H := by
  constructor
  · exact div_pos hτ.1 hσ
  · exact (div_lt_iff₀ hσ).2 (by nlinarith [hτ.2])

lemma normalize_continuous {σ H : ℝ} (hσ : 0 < σ) {f : ℝ → State}
    (hf : ContinuousOn f (Icc 0 H)) :
    ContinuousOn (normalize σ f) (Icc 0 (σ * H)) := by
  apply continuousOn_pi.mpr
  intro i
  exact ((continuous_apply i).comp_continuousOn
    (hf.comp (continuous_id.div_const σ).continuousOn
      (fun τ hτ => div_mem_Icc hσ hτ))).div_const _

/-- Chain rule for the actual plant, including continuity at both endpoints. -/
theorem normalize_trajectory {σ H : ℝ} (hσ : 0 < σ)
    {r b : ℝ → ℝ} {f : ℝ → State} (hf : IsTrajectory H r b f) :
    IsTrajectory (σ * H) (fun τ => r (τ/σ)/σ)
      (fun τ => b (τ/σ)/σ^2) (normalize σ f) := by
  constructor
  · exact normalize_continuous hσ hf.continuous
  · intro τ hτ i
    have hd := ((hf.ode (τ/σ) (div_mem_Ioo hσ hτ) i).comp τ
      ((hasDerivAt_id τ).div_const σ)).div_const (σ^i.val)
    convert hd using 1
    all_goals fin_cases i <;> simp [normalize, scaleState]
    all_goals field_simp

/-- The same chain rule transports position, velocity, acceleration, and jerk. -/
theorem normalize_reference {σ H : ℝ} (hσ : 0 < σ)
    {q : ℝ → State} {j : ℝ → ℝ}
    (hq : ∀ t ∈ Ioo 0 H, ∀ i : Fin 3,
      HasDerivAt (fun s => q s i) (![q t 1, q t 2, j t] i) t) :
    ∀ τ ∈ Ioo 0 (σ*H), ∀ i : Fin 3,
      HasDerivAt (fun s => normalize σ q s i)
        (![normalize σ q τ 1, normalize σ q τ 2, j (τ/σ)/σ^3] i) τ := by
  intro τ hτ i
  have hd := ((hq (τ/σ) (div_mem_Ioo hσ hτ) i).comp τ
    ((hasDerivAt_id τ).div_const σ)).div_const (σ^i.val)
  convert hd using 1
  all_goals fin_cases i <;> simp [normalize, scaleState]
  all_goals field_simp

lemma normalized_input {σ : ℝ} (hσ : 0 < σ)
    (f q : ℝ → State) (j w : ℝ → ℝ) (τ : ℝ) :
    (physicalInput σ f q j (τ/σ) + w (τ/σ)) / σ^2 =
      input (5/48) (normalize σ f) (normalize σ q)
        (fun u => j (u/σ)/σ^3) τ + w (τ/σ)/σ^2 := by
  dsimp [physicalInput, input, normalize, scaleState, error, command]
  field_simp
  ring

lemma normalized_error (σ : ℝ) (f q : ℝ → State) (τ : ℝ) :
    error (normalize σ f) (normalize σ q) τ = scaledError σ f q (τ/σ) := by
  funext i
  simp [error, normalize, scaledError, scaleState, sub_div]

/-- The normalized error budget is exactly the physical error budget divided
by the square of the rate scale. -/
lemma normalized_budget {σ R W J : ℝ} (hσ : 0 < σ)
    (hb : W + J/(48*σ) ≤ 2*σ^2*R) :
    W/σ^2 + (1/48)*(J/σ^3) ≤ 2*R := by
  calc
    W/σ^2 + (1/48)*(J/σ^3) = (W+J/(48*σ))/σ^2 := by field_simp
    _ ≤ (2*σ^2*R)/σ^2 := div_le_div_of_nonneg_right hb (sq_nonneg σ)
    _ = 2*R := by field_simp

/-- A physical plant with rate in [8σ,12σ] stays in the scaled error cube.
The plant and reference ODEs are transformed by proved chain rules. -/
theorem tracking_cube_scaled {σ H R W J : ℝ}
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
    ∀ t ∈ Icc 0 H, ∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R := by
  have hfn : IsTrajectory (σ*H) (fun τ => r (τ/σ)/σ)
      (fun τ => input (5/48) (normalize σ f) (normalize σ q)
        (fun u => j (u/σ)/σ^3) τ + w (τ/σ)/σ^2) (normalize σ f) := by
    simpa only [normalized_input hσ] using normalize_trajectory hσ hf
  have hlo (τ : ℝ) (hτ : τ ∈ Icc 0 (σ*H)) : 8 ≤ r (τ/σ)/σ :=
    (le_div_iff₀ hσ).2 (hrlo _ (div_mem_Icc hσ hτ))
  have hhi (τ : ℝ) (hτ : τ ∈ Icc 0 (σ*H)) : r (τ/σ)/σ ≤ 12 :=
    (div_le_iff₀ hσ).2 (hrhi _ (div_mem_Icc hσ hτ))
  have hcube := tracking_cube (mul_nonneg hσ.le hH) hR (by norm_num : (0:ℝ) ≤ 1/48)
    hfn (normalize_continuous hσ hq) (normalize_reference hσ hdq) hlo hhi
    (fun τ hτ => centered_reciprocal_bound (hlo τ hτ) (hhi τ hτ))
    (W := W/σ^2) (J := J/σ^3)
    (fun τ hτ => by
      rw [abs_div, abs_of_pos (pow_pos hσ 2)]
      exact div_le_div_of_nonneg_right (hw _ (div_mem_Icc hσ hτ)) (sq_nonneg σ))
    (fun τ hτ => by
      rw [abs_div, abs_of_pos (pow_pos hσ 3)]
      exact div_le_div_of_nonneg_right (hj _ (div_mem_Icc hσ hτ)) (pow_nonneg hσ.le 3))
    (normalized_budget hσ budget)
    (by simpa only [normalized_error, zero_div] using hi)
  intro t ht i
  have htime : σ*t/σ = t := by field_simp
  simpa only [normalized_error, htime] using
    hcube (σ*t) ⟨mul_nonneg hσ.le ht.1, mul_le_mul_of_nonneg_left ht.2 hσ.le⟩ i

/-- Unpack the normalized cube in physical units. -/
theorem scaled_cube_physical_bounds {σ R : ℝ} (hσ : 0 < σ) {s : State}
    (hz : ∀ i, |coordinates 0 (scaleState σ s) i| ≤ R) :
    |s 0| ≤ R ∧ |s 1| ≤ 8*σ*R ∧ |s 2| ≤ 64*σ^2*R ∧
      |σ^2 * command 0 (scaleState σ s)| ≤ 24*σ^2*R := by
  obtain ⟨hx,hv,ha,hc⟩ := cube_physical_bounds hz
  have hv' : |s 1|/σ ≤ 8*R := by
    simpa [scaleState, abs_div, abs_of_pos hσ] using hv
  have ha' : |s 2|/σ^2 ≤ 64*R := by
    simpa [scaleState, abs_div, abs_of_pos (pow_pos hσ 2)] using ha
  refine ⟨by simpa [scaleState] using hx, ?_, ?_, ?_⟩
  · have := (div_le_iff₀ hσ).mp hv'
    nlinarith
  · have := (div_le_iff₀ (pow_pos hσ 2)).mp ha'
    nlinarith
  · rw [abs_mul, abs_of_nonneg (sq_nonneg σ)]
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg σ)]

lemma physical_input_eq {σ : ℝ} (hσ : 0 < σ)
    (f q : ℝ → State) (j : ℝ → ℝ) (t : ℝ) :
    physicalInput σ f q j t = q t 2 + σ^2 * command 0 (scaledError σ f q t) +
      (5/(48*σ))*j t := by
  dsimp [physicalInput, scaledError, scaleState, error, command]
  field_simp
  ring

/-- Explicit travel and actuator margins in physical units. -/
theorem physical_margins_scaled {σ R L U V A J W : ℝ} (hσ : 0 < σ)
    {f q : ℝ → State} {j w : ℝ → ℝ} {t : ℝ}
    (hz : ∀ i, |coordinates 0 (scaledError σ f q t) i| ≤ R)
    (hq : q t 0 ∈ Icc (L+R) (U-R))
    (hv : |q t 1| ≤ V) (ha : |q t 2| ≤ A)
    (hj : |j t| ≤ J) (hw : |w t| ≤ W) :
    f t 0 ∈ Icc L U ∧ |f t 1| ≤ V+8*σ*R ∧ |f t 2| ≤ A+64*σ^2*R ∧
      |physicalInput σ f q j t+w t| ≤ A+24*σ^2*R+(5/(48*σ))*J+W := by
  obtain ⟨hx,hev,hea,hc⟩ := scaled_cube_physical_bounds hσ hz
  change |f t 0-q t 0| ≤ R at hx
  change |f t 1-q t 1| ≤ 8*σ*R at hev
  change |f t 2-q t 2| ≤ 64*σ^2*R at hea
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨hl,hu⟩ := abs_le.mp hx
    exact ⟨by linarith [hq.1],by linarith [hq.2]⟩
  · calc |f t 1| = |q t 1+(f t 1-q t 1)| := by congr 1; ring
         _ ≤ |q t 1|+|f t 1-q t 1| := abs_add_le _ _
         _ ≤ V+8*σ*R := add_le_add hv hev
  · calc |f t 2| = |q t 2+(f t 2-q t 2)| := by congr 1; ring
         _ ≤ |q t 2|+|f t 2-q t 2| := abs_add_le _ _
         _ ≤ A+64*σ^2*R := add_le_add ha hea
  · have hk : 0 ≤ (5:ℝ)/(48*σ) := by positivity
    have hj' : |(5/(48*σ))*j t| ≤ (5/(48*σ))*J := by
      rw [abs_mul, abs_of_nonneg hk]
      exact mul_le_mul_of_nonneg_left hj hk
    rw [physical_input_eq hσ]
    calc
      _ ≤ |q t 2+σ^2*command 0 (scaledError σ f q t)+(5/(48*σ))*j t|+|w t| :=
        abs_add_le _ _
      _ ≤ |q t 2+σ^2*command 0 (scaledError σ f q t)|+|(5/(48*σ))*j t|+W :=
        add_le_add (abs_add_le _ _) hw
      _ ≤ (|q t 2|+|σ^2*command 0 (scaledError σ f q t)|)+(5/(48*σ))*J+W := by
        exact add_le_add (add_le_add (abs_add_le _ _) hj') le_rfl
      _ ≤ A+24*σ^2*R+(5/(48*σ))*J+W := by
        exact add_le_add (add_le_add (add_le_add ha hc) le_rfl) le_rfl

/-- Finite replans preserve the physical tracking certificate when both the
physical state and reference state match at each switch. Each segment has its
own interior ODE. No derivative is asserted at a switch. -/
theorem finite_replans_scaled {N : ℕ} {σ R W J : ℝ}
    (hσ : 0 < σ) (hR : 0 ≤ R)
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
    (budget : W+J/(48*σ) ≤ 2*σ^2*R)
    (hphysical : ∀ k, k+1 < N → f (k+1) 0 = f k (duration k))
    (hreference : ∀ k, k+1 < N → q (k+1) 0 = q k (duration k))
    (hi : ∀ i, |coordinates 0 (scaledError σ (f 0) (q 0) 0) i| ≤ R) :
    ∀ k < N, ∀ t ∈ Icc 0 (duration k), ∀ i,
      |coordinates 0 (scaledError σ (f k) (q k) t) i| ≤ R := by
  have hsegment : ∀ k < N,
      (∀ i, |coordinates 0 (scaledError σ (f k) (q k) 0) i| ≤ R) →
      ∀ t ∈ Icc 0 (duration k), ∀ i,
        |coordinates 0 (scaledError σ (f k) (q k) t) i| ≤ R := by
    intro k hk hstart
    exact tracking_cube_scaled hσ (hduration k hk) hR (hf k hk) (hq k hk)
      (hdq k hk) (hrlo k hk) (hrhi k hk) (hw k hk) (hj k hk) budget hstart
  have hstart : ∀ k, k < N → ∀ i,
      |coordinates 0 (scaledError σ (f k) (q k) 0) i| ≤ R := by
    intro k
    induction k with
    | zero => exact fun _ => hi
    | succ k ih =>
      intro hk i
      change |coordinates 0 (scaleState σ (error (f (k+1)) (q (k+1)) 0)) i| ≤ R
      rw [matched_error (hphysical k hk) (hreference k hk)]
      exact hsegment k (by omega) (ih (by omega)) (duration k)
        ⟨hduration k (by omega),le_rfl⟩ i
  exact fun k hk => hsegment k hk (hstart k hk)

/-- Illustrative arithmetic only: σ=10/s, W=.01 m/s², J=10 m/s³,
and R=.2 mm satisfy the residual budget. These are not measured parameters. -/
theorem illustrative_budget :
    (1:ℝ)/100 + 10/(48*10) ≤ 2*10^2*(1/5000) := by norm_num

end LeanControls.ScaledTracking
