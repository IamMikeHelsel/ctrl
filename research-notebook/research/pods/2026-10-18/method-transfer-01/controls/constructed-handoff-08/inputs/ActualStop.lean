module
public import ComparisonEnvelope
public import FirstStop
public import StoppingCertificate

/-! A delayed stopping contract for an actual classical trajectory. Position is
measured from the estimated reference; this is a one-sided travel limit, not a
bound on displacement from an unknown actual initial position. A first zero of
velocity is certified; no maintained-rest or friction-brake model is asserted. -/
@[expose] public section
noncomputable section
namespace LeanControls.ActualStop
open Set
open UncertainLag (State heldSolution)
open VariableResponse StoppingCertificate

/-- During engagement delay, only the kinematic equations are prescribed.
The pending acceleration bound is supplied separately, including endpoints. -/
structure IsDelayTrajectory (D : ℝ) (f : ℝ → State) : Prop where
  continuous : ContinuousOn f (Icc 0 D)
  position_deriv : ∀ t ∈ Ioo 0 D, HasDerivAt (fun s => f s 0) (f t 1) t
  velocity_deriv : ∀ t ∈ Ioo 0 D, HasDerivAt (fun s => f s 1) (f t 2) t

/-- A reusable delay enclosure from a bound on pending acceleration. -/
theorem delay_coordinate_upper {D xHi vHi aHi : ℝ} (hD : 0 ≤ D)
    {f : ℝ → State} (hf : IsDelayTrajectory D f)
    (hx : f 0 0 ≤ xHi) (hv : f 0 1 ≤ vHi)
    (ha : ∀ t ∈ Icc 0 D, f t 2 ≤ aHi) :
    ∀ t ∈ Icc 0 D,
      f t 0 ≤ xHi + vHi*t + aHi*t^2/2 ∧ f t 1 ≤ vHi+aHi*t := by
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hvd (t : ℝ) : HasDerivAt (fun s : ℝ => vHi+aHi*s) aHi t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul aHi).const_add vHi
  have hvbound : ∀ t ∈ Icc 0 D, f t 1 ≤ vHi+aHi*t :=
    derivative_comparison hD (hfc 1) (by fun_prop) hf.velocity_deriv
      (fun t _ => hvd t) (by simpa using hv)
      (fun t ht => ha t ⟨ht.1.le, ht.2.le⟩)
  have hxd (t : ℝ) : HasDerivAt (fun s : ℝ => xHi+vHi*s+aHi*s^2/2)
      (vHi+aHi*t) t := by
    convert (((hasDerivAt_id t).const_mul vHi).const_add xHi).add
      ((((hasDerivAt_id t).pow 2).const_mul aHi).div_const 2) using 1
    · funext s
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hxbound : ∀ t ∈ Icc 0 D, f t 0 ≤ xHi+vHi*t+aHi*t^2/2 :=
    derivative_comparison hD (hfc 0) (by fun_prop) hf.position_deriv
      (fun t _ => hxd t) (by simpa using hx)
      (fun t ht => hvbound t ⟨ht.1.le, ht.2.le⟩)
  exact fun t ht => ⟨hxbound t ht, hvbound t ht⟩

/-- The concrete delay assumptions imply the engagement box and also bound
every position in the delay interval, including the zero-delay case. -/
theorem delay_engagement {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1/20)
    {f : ℝ → State} (hf : IsDelayTrajectory D f)
    (hx : f 0 0 ≤ 1/1000) (hv : f 0 1 ≤ 41/100)
    (ha : ∀ t ∈ Icc 0 D, f t 2 ≤ 1/10) :
    (∀ i : Fin 3, f D i ≤ engagementUpper i) ∧
      ∀ t ∈ Icc 0 D, f t 0 ≤ 3/20 := by
  have hbound := delay_coordinate_upper hD0 hf hx hv ha
  have hend := hbound D ⟨hD0, le_rfl⟩
  have harith := delay_state_arithmetic hD0 hD1
  constructor
  · intro i
    fin_cases i
    · exact hend.1.trans harith.1
    · exact hend.2.trans harith.2
    · exact ha D ⟨hD0, le_rfl⟩
  · intro t ht
    exact (hbound t ht).1.trans
      ((delay_state_arithmetic ht.1 (ht.2.trans hD1)).1.trans
        (by norm_num [engagementUpper]))

/-- A continuous actual state with bounded engagement delay and changing brake
response reaches its first zero velocity by 0.55 seconds, without exceeding
the 0.15 metre reference-relative position limit before that event. The
acceleration target may be stronger than -1.2; it need not be constant.
No positive velocity at engagement, terminal bound, or safety premise is used. -/
theorem delayed_actual_first_stop {D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1/20)
    {f : ℝ → State} {r b : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 (D+1/2)))
    (hdelay : IsDelayTrajectory D f)
    (hx : f 0 0 ≤ 1/1000) (hv0 : 0 ≤ f 0 1) (hv1 : f 0 1 ≤ 41/100)
    (ha : ∀ t ∈ Icc 0 D, f t 2 ≤ 1/10)
    (hbrake : IsTrajectory (1/2) r b (fun t => f (D+t)))
    (hrc : ContinuousOn r (Icc 0 (1/2)))
    (hrlo : ∀ t ∈ Icc 0 (1/2), 8 ≤ r t)
    (hrhi : ∀ t ∈ Icc 0 (1/2), r t ≤ 12)
    (hb : ∀ t ∈ Icc 0 (1/2), b t ≤ -6/5) :
    ∃ T ∈ Icc 0 (D+1/2), T ≤ 11/20 ∧ f T 1 = 0 ∧
      (∀ t ∈ Ico 0 T, 0 < f t 1) ∧ ∀ t ∈ Icc 0 T, f t 0 ≤ 3/20 := by
  obtain ⟨hinit, hprefix⟩ := delay_engagement hD0 hD1 hdelay hx hv1 ha
  have hu := upper_flow_bound (rlo := 8) (rhi := 12) (bHi := -6/5)
    (zHi := engagementUpper) (by norm_num : (0:ℝ) ≤ 1/2) hrc
    (by norm_num) hrlo hrhi hb hbrake (by simpa using hinit)
  have hrate : upperRate 8 12 (engagementUpper 2) (-6/5) = 8 := by
    norm_num [upperRate, engagementUpper]
  rw [hrate] at hu
  have hvend : f (D+1/2) 1 ≤ 0 :=
    (hu (1/2) ⟨by norm_num, le_rfl⟩ 1).trans upper_velocity_by_half_second
  have hpath : ∀ t ∈ Icc 0 (D+1/2), f t 0 ≤ 3/20 := by
    intro t ht
    by_cases htd : t ≤ D
    · exact hprefix t ⟨ht.1, htd⟩
    · have hs : t-D ∈ Icc 0 (1/2) := ⟨by linarith, by linarith [ht.2]⟩
      have h := (hu (t-D) hs 0).trans (upper_position_le hs.1)
      simpa only [add_sub_cancel] using h
  obtain ⟨T, hT, hzero, hbefore, htravel⟩ :=
    FirstStop.first_zero_with_travel_bound (by linarith : 0 ≤ D+1/2)
      ((continuous_apply 1).comp_continuousOn hfc) hv0 hvend hpath
  exact ⟨T, hT, by linarith [hT.2], hzero, hbefore, htravel⟩

/-- The classical trajectory class has explicit analytic instances. This is
not an existence theorem for every bounded, possibly rough target signal. -/
theorem constant_flow_isTrajectory {R : ℝ} (hR : R ≠ 0) (H u : ℝ) (z : State) :
    IsTrajectory H (fun _ => R) (fun _ => u) (fun t => heldSolution R t u z) := by
  constructor
  · exact (continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
      (UncertainLag.exact_ode hR u t z i).continuousAt).continuousOn
  · intro t _ i
    exact UncertainLag.exact_ode hR u t z i

/-- Changing the time origin preserves the actual autonomous flow equations. -/
theorem constant_flow_shift_isTrajectory {R : ℝ} (hR : R ≠ 0) (H D u : ℝ)
    (z : State) :
    IsTrajectory H (fun _ => R) (fun _ => u) (fun t => heldSolution R (D+t) u z) := by
  have hc : Continuous (fun t => heldSolution R t u z) :=
    continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
      (UncertainLag.exact_ode hR u t z i).continuousAt
  constructor
  · exact (hc.comp (continuous_const.add continuous_id)).continuousOn
  · intro t _ i
    convert (UncertainLag.exact_ode hR u (D+t) z i).comp t
      ((hasDerivAt_id t).const_add D) using 1 <;>
      simp only [Function.comp_def, id_eq, mul_one]

/-- An explicit analytic flow satisfies the complete delayed stopping contract.
It starts braking immediately, so it is an allowed faster response, not the
worst allowed delay. The declared engagement boundary is 0.05 seconds. -/
theorem constant_response_example :
    ∃ T ∈ Icc (0:ℝ) (11/20),
      heldSolution 8 T (-6/5) ![0,2/5,0] 1 = 0 ∧
      (∀ t ∈ Ico 0 T, 0 < heldSolution 8 t (-6/5) ![0,2/5,0] 1) ∧
      ∀ t ∈ Icc 0 T, heldSolution 8 t (-6/5) ![0,2/5,0] 0 ≤ 3/20 := by
  let f : ℝ → State := fun t => heldSolution 8 t (-6/5) ![0,2/5,0]
  have hc : Continuous f := continuous_pi fun i =>
    continuous_iff_continuousAt.mpr fun t =>
      (UncertainLag.exact_ode (by norm_num : (8:ℝ) ≠ 0) (-6/5) t ![0,2/5,0] i).continuousAt
  have hd : IsDelayTrajectory (1/20) f := by
    refine ⟨hc.continuousOn, ?_, ?_⟩
    · intro t _
      exact UncertainLag.exact_ode (by norm_num) (-6/5) t ![0,2/5,0] 0
    · intro t _
      exact UncertainLag.exact_ode (by norm_num) (-6/5) t ![0,2/5,0] 1
  have ha : ∀ t ∈ Icc 0 (1/20), f t 2 ≤ 1/10 := by
    intro t ht
    have he : Real.exp (-(8*t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    norm_num [f, heldSolution]
    linarith
  obtain ⟨T, hT, _, hz, hb, hp⟩ := delayed_actual_first_stop
    (D := 1/20) (f := f) (r := fun _ => 8) (b := fun _ => -6/5)
    (by norm_num) (by norm_num) hc.continuousOn hd
    (by norm_num [f, UncertainLag.exact_initial])
    (by norm_num [f, UncertainLag.exact_initial])
    (by norm_num [f, UncertainLag.exact_initial]) ha
    (constant_flow_shift_isTrajectory (by norm_num) (1/2) (1/20) (-6/5) ![0,2/5,0])
    continuousOn_const (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
  exact ⟨T, by norm_num at hT ⊢; exact hT, hz, hb, hp⟩

end LeanControls.ActualStop
#print axioms LeanControls.ActualStop.delay_coordinate_upper
#print axioms LeanControls.ActualStop.delay_engagement
#print axioms LeanControls.ActualStop.delayed_actual_first_stop
#print axioms LeanControls.ActualStop.constant_flow_isTrajectory
#print axioms LeanControls.ActualStop.constant_flow_shift_isTrajectory
#print axioms LeanControls.ActualStop.constant_response_example
