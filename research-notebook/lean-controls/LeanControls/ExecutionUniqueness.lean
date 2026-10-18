module
public import LeanControls.UncertainExecution
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Uniqueness from the differential-equation specification. Continuity is
required across the closed sample intervals, while derivatives are required only
in their interiors; no derivative at a switching time is assumed. -/
@[expose] public section
noncomputable section
namespace LeanControls.ExecutionUniqueness
open Set
open UncertainLag (State vectorField heldSegment input)
open SamplingClock

/-- Zero interior derivative and closed-interval continuity determine every
value from the left endpoint, including the right endpoint. -/
theorem constant_of_interior_derivative_zero {a b : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) :
    ∀ t ∈ Icc a b, f t = f a := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | hlt
  · rw [← heq]
  · obtain ⟨c, hc', hslope⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hlt
      (hc.mono (Icc_subset_Icc_right ht.2))
      (fun s hs => hd s ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩)
    have hne : t - a ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    have hzero : f t - f a = 0 := by
      simpa [div_eq_zero_iff, hne] using hslope.symm
    exact sub_eq_zero.mp hzero

/-- Two continuous solutions of the same held-command actuator-lag ODE agree
on the whole closed interval when they agree at its initial endpoint. The rate
and command may be arbitrary real numbers; uniqueness does not require stability. -/
theorem held_ode_unique {a b r u : ℝ} {f g : ℝ → State}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, ∀ i : Fin 3,
      HasDerivAt (fun s => f s i) (vectorField r u (f t) i) t)
    (hg' : ∀ t ∈ Ioo a b, ∀ i : Fin 3,
      HasDerivAt (fun s => g s i) (vectorField r u (g t) i) t)
    (hi : f a = g a) : EqOn f g (Icc a b) := by
  have hfc (i : Fin 3) : ContinuousOn (fun t => f t i) (Icc a b) :=
    (continuous_apply i).comp_continuousOn hf
  have hgc (i : Fin 3) : ContinuousOn (fun t => g t i) (Icc a b) :=
    (continuous_apply i).comp_continuousOn hg
  have hacc : ∀ t ∈ Icc a b, f t 2 = g t 2 := by
    have hzero := constant_of_interior_derivative_zero
      (((hfc 2).sub (hgc 2)).mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
      (fun t ht => show HasDerivAt
        (fun s => (f s 2 - g s 2) * Real.exp (r*s)) 0 t from by
        convert! ((hf' t ht 2).sub (hg' t ht 2)).mul
          (((hasDerivAt_id t).const_mul r).exp) using 1
        simp [vectorField, Pi.sub_apply]
        ring)
    intro t ht
    have hh := hzero t ht
    dsimp only [Pi.sub_apply, Pi.mul_apply] at hh
    rw [hi] at hh
    simp only [sub_self, zero_mul] at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero _))
  have hvel : ∀ t ∈ Icc a b, f t 1 = g t 1 := by
    have hzero := constant_of_interior_derivative_zero ((hfc 1).sub (hgc 1))
      (fun t ht => show HasDerivAt (fun s => f s 1 - g s 1) 0 t from by
        have hd := (hf' t ht 1).sub (hg' t ht 1)
        simpa [vectorField, hacc t ⟨ht.1.le, ht.2.le⟩] using! hd)
    intro t ht
    have hh := hzero t ht
    dsimp only [Pi.sub_apply, Pi.mul_apply] at hh
    rw [hi] at hh
    simpa only [sub_self, sub_eq_zero] using hh
  have hpos : ∀ t ∈ Icc a b, f t 0 = g t 0 := by
    have hzero := constant_of_interior_derivative_zero ((hfc 0).sub (hgc 0))
      (fun t ht => show HasDerivAt (fun s => f s 0 - g s 0) 0 t from by
        have hd := (hf' t ht 0).sub (hg' t ht 0)
        simpa [vectorField, hvel t ⟨ht.1.le, ht.2.le⟩] using! hd)
    intro t ht
    have hh := hzero t ht
    dsimp only [Pi.sub_apply, Pi.mul_apply] at hh
    rw [hi] at hh
    simpa only [sub_self, sub_eq_zero] using hh
  intro t ht
  ext i
  fin_cases i
  · exact hpos t ht
  · exact hvel t ht
  · exact hacc t ht

/-- The analytic held solution represents any continuous trajectory satisfying
the held ODE on the interval interior. -/
theorem eq_heldSegment {a b r u : ℝ} (hr : r ≠ 0) {f : ℝ → State}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, ∀ i : Fin 3,
      HasDerivAt (fun s => f s i) (vectorField r u (f t) i) t) :
    EqOn f (fun t => heldSegment r (t-a) (f a) u) (Icc a b) := by
  have hder (t : ℝ) (i : Fin 3) :
      HasDerivAt (fun s => heldSegment r (s-a) (f a) u i)
        (vectorField r u (heldSegment r (t-a) (f a) u) i) t := by
    simpa using! (UncertainLag.heldSegment_ode hr (t-a) (f a) u i).comp t
      ((hasDerivAt_id t).sub_const a)
  apply held_ode_unique hc
    ((continuous_pi (fun i => continuous_iff_continuousAt.mpr
      (fun t => (hder t i).continuousAt))).continuousOn) hd
    (fun t _ i => hder t i)
  simp [UncertainLag.heldSegment_zero]

/-- A trajectory specified independently by continuity, an initial value, and
the held-input ODE. The command uses this trajectory's own sampled state. Errors
are fixed scalars on each interval, with post-clamp error inside the rate factor. -/
structure IsExecution (r : ℝ) (h e d : ℕ → ℝ) (z0 : State) (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Ici 0)
  initial : f 0 = z0
  ode : ∀ n, ∀ t ∈ Ioo (sampleTime h n) (sampleTime h (n+1)), ∀ i : Fin 3,
    HasDerivAt (fun s => f s i)
      (vectorField r (RobustPD.saturate 1 (input (f (sampleTime h n)) + e n) + d n)
        (f t) i) t

/-- The independently stated execution conditions are inhabited by the explicit
trajectory; no uniqueness or safety assumption is built into `IsExecution`. -/
theorem constructed_isExecution (r : ℝ) (hr : r ≠ 0) (h e d : ℕ → ℝ) (z0 : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n) :
    IsExecution r h e d z0 (UncertainTravel.state r h e d z0) := by
  refine ⟨UncertainExecution.state_continuousOn_nonnegative r hr h e d z0 hmin0 hlo, ?_, ?_⟩
  · have hh := UncertainTravel.state_at_sample r h e d z0 hmin0 hlo 0
    simpa [UncertainTravel.samples_zero] using hh
  · intro n t ht i
    rw [UncertainTravel.state_at_sample r h e d z0 hmin0 hlo n]
    exact UncertainExecution.state_ode_interior r hr h e d z0 hmin0 hlo n ht.1 ht.2 i

/-- Induction over the samples transfers the actual sampled feedback, rather
than assuming that an independent trajectory already uses our recursive samples. -/
theorem samples_eq_of_execution (r : ℝ) (hr : r ≠ 0) (h e d : ℕ → ℝ) (z0 : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : IsExecution r h e d z0 f) :
    ∀ n, f (sampleTime h n) = UncertainTravel.samples r h e d z0 n := by
  intro n
  induction n with
  | zero => simpa [UncertainTravel.samples_zero] using hf.initial
  | succ n ih =>
    have hn0 : 0 ≤ sampleTime h n :=
      (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
    have horder : sampleTime h n ≤ sampleTime h (n+1) :=
      (sampleTime_strictMono h hmin0 hlo (Nat.lt_succ_self n)).le
    have heq := eq_heldSegment hr
      (hf.continuous.mono (fun t ht => hn0.trans ht.1)) (hf.ode n)
    calc
      f (sampleTime h (n+1)) = heldSegment r
          (sampleTime h (n+1) - sampleTime h n) (f (sampleTime h n))
          (RobustPD.saturate 1 (input (f (sampleTime h n)) + e n) + d n) :=
        heq ⟨horder, le_rfl⟩
      _ = UncertainTravel.samples r h e d z0 (n+1) := by
        simp [sampleTime_succ, ih, UncertainTravel.samples_succ, UncertainTravel.segment]

/-- Every continuous trajectory satisfying the sampled held-input equations
equals the constructed execution at every nonnegative real time. Positive dwell
time prevents accumulation of infinitely many sample boundaries at finite time. -/
theorem execution_eq_state (r : ℝ) (hr : r ≠ 0) (h e d : ℕ → ℝ) (z0 : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f : ℝ → State} (hf : IsExecution r h e d z0 f) :
    EqOn f (UncertainTravel.state r h e d z0) (Ici 0) := by
  have hsamples := samples_eq_of_execution r hr h e d z0 hmin0 hlo hf
  intro t ht
  obtain ⟨n, hnlo, hnhi⟩ := exists_segment h hmin0 hlo ht
  have hn0 : 0 ≤ sampleTime h n :=
    (mul_nonneg (Nat.cast_nonneg n) hmin0.le).trans (sampleTime_lower h hlo n)
  have heq := eq_heldSegment hr
    (hf.continuous.mono (fun t ht => hn0.trans ht.1)) (hf.ode n)
  rw [UncertainExecution.state_on_interval r hr h e d z0 hmin0 hlo n ⟨hnlo, hnhi.le⟩]
  simpa [hsamples n, UncertainTravel.segment] using heq ⟨hnlo, hnhi.le⟩

/-- The differential-equation specification has at most one continuous execution
on nonnegative time, independently of the energy and error-budget assumptions. -/
theorem execution_unique (r : ℝ) (hr : r ≠ 0) (h e d : ℕ → ℝ) (z0 : State)
    {hmin : ℝ} (hmin0 : 0 < hmin) (hlo : ∀ n, hmin ≤ h n)
    {f g : ℝ → State} (hf : IsExecution r h e d z0 f)
    (hg : IsExecution r h e d z0 g) : EqOn f g (Ici 0) := by
  intro t ht
  exact (execution_eq_state r hr h e d z0 hmin0 hlo hf ht).trans
    (execution_eq_state r hr h e d z0 hmin0 hlo hg ht).symm

/-- All-time travel safety applies to any continuous solution of the actual
sampled clipped-feedback ODE, not just the analytic trajectory definition. -/
theorem execution_travel_limit {r : ℝ} (hrlo : 9/10 ≤ r) (hrhi : r ≤ 11/10)
    (h e d : ℕ → ℝ) (z0 : State) {hmin : ℝ} (hmin0 : 0 < hmin)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1/5)
    (hbudget : ∀ n, |e n| + |d n| ≤ 1/90) (hz : UncertainTravel.V z0 ≤ 12)
    {f : ℝ → State} (hf : IsExecution r h e d z0 f) {t : ℝ} (ht : 0 ≤ t) :
    |f t 0| ≤ 2 := by
  rw [execution_eq_state r (ne_of_gt (by linarith)) h e d z0 hmin0 hlo hf ht]
  exact UncertainTravel.travel_limit hrlo hrhi h e d z0 hmin0 hlo hhi hbudget hz ht

end LeanControls.ExecutionUniqueness
