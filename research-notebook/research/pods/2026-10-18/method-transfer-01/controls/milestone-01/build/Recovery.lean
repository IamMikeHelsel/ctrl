module
public import ActualStop

/-! A symbolic first-zero contract for restored effective braking with lag.
The target q is actual effective acceleration authority, not actuator effort.
One continuous physical state spans both phases. The state is supplied; this
file does not prove general initial-value existence or permanent rest. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.Recovery
open Set
open UncertainLag (State heldSolution)
open VariableResponse

def velocityBudget (v0 A T b k : ℝ) : ℝ := v0 + A*T + (A+b)/k
def travelBudget (v0 A T b k : ℝ) : ℝ :=
  v0*T + A*T^2/2 + (velocityBudget v0 A T b k)^2/(2*b)
def recoveryHorizon (v0 A T b k : ℝ) : ℝ := velocityBudget v0 A T b k / b

/-- The loss-phase acceleration envelope follows from the actual lag ODE.
It is not an acceleration-envelope premise of the final result. -/
theorem loss_acceleration_upper {T A : ℝ} (hT : 0 ≤ T)
    {r q : ℝ → ℝ} {f : ℝ → State}
    (hrc : ContinuousOn r (Icc 0 T))
    (hr : ∀ t ∈ Icc 0 T, 0 ≤ r t)
    (hq : ∀ t ∈ Icc 0 T, q t ≤ A)
    (hf : IsTrajectory T r q f) (ha : f 0 2 ≤ A) :
    ∀ t ∈ Icc 0 T, f t 2 ≤ A := by
  apply linear_comparison hT hrc
    ((continuous_apply 2).comp_continuousOn hf.continuous) continuousOn_const
    (fun t ht => hf.ode t ht 2) (fun t _ => hasDerivAt_const t A) ha
  intro t ht
  have h := mul_nonpos_of_nonneg_of_nonpos (hr t ⟨ht.1.le, ht.2.le⟩)
    (sub_nonpos.mpr (hq t ⟨ht.1.le, ht.2.le⟩))
  change r t * (q t - f t 2) - 0 + r t * (f t 2 - A) ≤ 0
  nlinarith

/-- A lower rate bound suffices when the upper acceleration starts above the
negative target. No upper response-rate bound is required. -/
theorem recovered_upper_flow {S k b : ℝ} (hS : 0 ≤ S) (hk : 0 < k)
    {r q : ℝ → ℝ} {f : ℝ → State} {z : State}
    (hrc : ContinuousOn r (Icc 0 S))
    (hr : ∀ t ∈ Icc 0 S, k ≤ r t)
    (hq : ∀ t ∈ Icc 0 S, q t ≤ -b)
    (hf : IsTrajectory S r q f) (hz : -b ≤ z 2)
    (hi : ∀ i : Fin 3, f 0 i ≤ z i) :
    ∀ t ∈ Icc 0 S, ∀ i : Fin 3, f t i ≤ heldSolution k t (-b) z i := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hfc (i : Fin 3) := (continuous_apply i).comp_continuousOn hf.continuous
  have hc (i : Fin 3) : ContinuousOn (fun t => heldSolution k t (-b) z i) (Icc 0 S) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (UncertainLag.exact_ode hk0 (-b) t z i).continuousAt).continuousOn
  have hd (i : Fin 3) (t : ℝ) := UncertainLag.exact_ode hk0 (-b) t z i
  have hinit (i : Fin 3) : f 0 i ≤ heldSolution k 0 (-b) z i := by
    simpa only [UncertainLag.exact_initial] using hi i
  have ha : ∀ t ∈ Icc 0 S, f t 2 ≤ heldSolution k t (-b) z 2 := by
    apply linear_comparison hS hrc (hfc 2) (hc 2)
      (fun t ht => hf.ode t ht 2) (fun t _ => hd 2 t) (hinit 2)
    intro t ht
    have htc : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le⟩
    have hrt : 0 ≤ r t := (hk.trans_le (hr t htc)).le
    have htarget := mul_le_mul_of_nonneg_left (hq t htc) hrt
    have hgap : 0 ≤ heldSolution k t (-b) z 2 + b := by
      change 0 ≤ -b + (z 2 - -b) * Real.exp (-k*t) + b
      nlinarith [mul_nonneg (show 0 ≤ z 2 + b by linarith) (Real.exp_pos (-k*t)).le]
    have hs := mul_nonneg (sub_nonneg.mpr (hr t htc)) hgap
    change r t*(q t-f t 2) - k*(-b-heldSolution k t (-b) z 2) +
      r t*(f t 2-heldSolution k t (-b) z 2) ≤ 0
    nlinarith
  have hv : ∀ t ∈ Icc 0 S, f t 1 ≤ heldSolution k t (-b) z 1 :=
    derivative_comparison hS (hfc 1) (hc 1)
      (fun t ht => hf.ode t ht 1) (fun t _ => hd 1 t) (hinit 1)
      (fun t ht => ha t ⟨ht.1.le, ht.2.le⟩)
  have hx : ∀ t ∈ Icc 0 S, f t 0 ≤ heldSolution k t (-b) z 0 :=
    derivative_comparison hS (hfc 0) (hc 0)
      (fun t ht => hf.ode t ht 0) (fun t _ => hd 0 t) (hinit 0)
      (fun t ht => hv t ⟨ht.1.le, ht.2.le⟩)
  intro t ht i
  fin_cases i
  · exact hx t ht
  · exact hv t ht
  · exact ha t ht

/-- Dropping the exponential transient gives a simple but conservative budget. -/
theorem relaxed_flow_bounds {X U A b k s : ℝ}
    (hA : 0 ≤ A) (hb : 0 < b) (hk : 0 < k) (hs : 0 ≤ s) :
    heldSolution k s (-b) ![X,U,A] 1 ≤ U + (A+b)/k - b*s ∧
    heldSolution k s (-b) ![X,U,A] 0 ≤ X + (U+(A+b)/k)^2/(2*b) := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hb0 : b ≠ 0 := ne_of_gt hb
  have he0 := (Real.exp_pos (-k*s)).le
  have he1 : Real.exp (-k*s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hC : 0 ≤ (A+b)/k := div_nonneg (by linarith) hk.le
  have hCE := mul_nonneg hC he0
  have hdrop : 0 ≤ (A+b)/k^2 * (1-Real.exp (-k*s)) :=
    mul_nonneg (div_nonneg (by linarith) (sq_nonneg k)) (by linarith)
  have hvel : heldSolution k s (-b) ![X,U,A] 1 =
      U + (A+b)/k - b*s - ((A+b)/k)*Real.exp (-k*s) := by
    dsimp [heldSolution]
    ring
  have hpos : heldSolution k s (-b) ![X,U,A] 0 =
      X + (U+(A+b)/k)*s - b*s^2/2 - (A+b)/k^2*(1-Real.exp (-k*s)) := by
    dsimp [heldSolution]
    ring
  constructor
  · rw [hvel]; linarith
  · rw [hpos]
    have hquad : (U+(A+b)/k)*s - b*s^2/2 ≤ (U+(A+b)/k)^2/(2*b) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*b)).mpr
      nlinarith [sq_nonneg (b*s-(U+(A+b)/k))]
    linarith

/-- Parameterized finite stopping time and forward-position bound. Recovery
starts at T, and its target and rate guarantees persist to the computed horizon.
All three physical coordinates are continuous across T. The conclusion ends at
the first zero of velocity; it does not claim maintained rest or lower safety. -/
theorem restored_braking_first_zero {X v0 A T b k : ℝ}
    (hv0 : 0 ≤ v0) (hA : 0 ≤ A) (hT : 0 ≤ T) (hb : 0 < b) (hk : 0 < k)
    {f : ℝ → State} {rLoss qLoss rBrake qBrake : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 (T + recoveryHorizon v0 A T b k)))
    (hLoss : IsTrajectory T rLoss qLoss f)
    (hrLossC : ContinuousOn rLoss (Icc 0 T))
    (hrLoss : ∀ t ∈ Icc 0 T, 0 ≤ rLoss t)
    (hqLoss : ∀ t ∈ Icc 0 T, qLoss t ≤ A)
    (hx : f 0 0 ≤ X) (hv : 0 ≤ f 0 1) (hvHi : f 0 1 ≤ v0) (ha : f 0 2 ≤ A)
    (hBrake : IsTrajectory (recoveryHorizon v0 A T b k) rBrake qBrake (fun s => f (T+s)))
    (hrBrakeC : ContinuousOn rBrake (Icc 0 (recoveryHorizon v0 A T b k)))
    (hrBrake : ∀ s ∈ Icc 0 (recoveryHorizon v0 A T b k), k ≤ rBrake s)
    (hqBrake : ∀ s ∈ Icc 0 (recoveryHorizon v0 A T b k), qBrake s ≤ -b) :
    ∃ τ ∈ Icc 0 (T + recoveryHorizon v0 A T b k),
      f τ 1 = 0 ∧ (∀ t ∈ Ico 0 τ, 0 < f t 1) ∧
      ∀ t ∈ Icc 0 τ, f t 0 ≤ X + travelBudget v0 A T b k := by
  have hV : 0 ≤ velocityBudget v0 A T b k := by
    dsimp [velocityBudget]; positivity
  have hS : 0 ≤ recoveryHorizon v0 A T b k := div_nonneg hV hb.le
  have haLoss := loss_acceleration_upper hT hrLossC hrLoss hqLoss hLoss ha
  have hDelay : ActualStop.IsDelayTrajectory T f :=
    ⟨hLoss.continuous, (fun t ht => hLoss.ode t ht 0), (fun t ht => hLoss.ode t ht 1)⟩
  have hprefix := ActualStop.delay_coordinate_upper hT hDelay hx hvHi haLoss
  have hend := hprefix T ⟨hT, le_rfl⟩
  have hinit : ∀ i : Fin 3, f (T+0) i ≤ ![X+v0*T+A*T^2/2,v0+A*T,A] i := by
    intro i
    fin_cases i
    · simpa using hend.1
    · simpa using hend.2
    · simpa using haLoss T ⟨hT, le_rfl⟩
  have hflow := recovered_upper_flow hS hk hrBrakeC hrBrake hqBrake hBrake
    (z := ![X+v0*T+A*T^2/2,v0+A*T,A]) (by dsimp; linarith) hinit
  have htail (s : ℝ) (hs : s ∈ Icc 0 (recoveryHorizon v0 A T b k)) :=
    relaxed_flow_bounds (X := X+v0*T+A*T^2/2) (U := v0+A*T) hA hb hk hs.1
  have hvend : f (T+recoveryHorizon v0 A T b k) 1 ≤ 0 := by
    have hh := (hflow _ ⟨hS, le_rfl⟩ 1).trans (htail _ ⟨hS, le_rfl⟩).1
    have heq : v0+A*T+(A+b)/k-b*recoveryHorizon v0 A T b k = 0 := by
      dsimp [recoveryHorizon, velocityBudget]
      field_simp
      ring
    linarith
  have hpath : ∀ t ∈ Icc 0 (T+recoveryHorizon v0 A T b k),
      f t 0 ≤ X+travelBudget v0 A T b k := by
    intro t ht
    by_cases hpre : t ≤ T
    · have hp := (hprefix t ⟨ht.1, hpre⟩).1
      have hlin := mul_le_mul_of_nonneg_left hpre hv0
      have hsq : t^2 ≤ T^2 := by nlinarith [ht.1]
      have hquad := mul_le_mul_of_nonneg_left hsq hA
      have hnonneg : 0 ≤ (velocityBudget v0 A T b k)^2/(2*b) := by positivity
      dsimp [travelBudget]
      nlinarith
    · have hs : t-T ∈ Icc 0 (recoveryHorizon v0 A T b k) := ⟨by linarith, by linarith [ht.2]⟩
      have hh := (hflow (t-T) hs 0).trans (htail (t-T) hs).2
      simpa only [add_sub_cancel, travelBudget, velocityBudget, add_assoc] using hh
  exact FirstStop.first_zero_with_travel_bound (add_nonneg hT hS)
    ((continuous_apply 1).comp_continuousOn hfc) hv hvend hpath

/-- Positive response speed with no effective braking has no finite stop or
forward-travel bound. This is an exact physical ODE counterexample. -/
def coast (t : ℝ) : State := ![t,1,0]

theorem no_recovery_counterexample :
    (∀ H : ℝ, IsTrajectory H (fun _ => 1) (fun _ => 0) coast) ∧
    (∀ t : ℝ, coast t 1 > 0) ∧
    (∀ L : ℝ, ∃ t ≥ 0, L < coast t 0) := by
  constructor
  · intro H
    constructor
    · exact (continuous_pi fun i => by fin_cases i <;> simp [coast] <;> fun_prop).continuousOn
    · intro t _ i
      fin_cases i
      · convert (hasDerivAt_id t) using 1 <;> simp [coast]
        rfl
      · simpa [coast] using hasDerivAt_const t (1:ℝ)
      · simpa [coast] using hasDerivAt_const t (0:ℝ)
  constructor
  · intro t; norm_num [coast]
  · intro L
    refine ⟨max 0 L+1, by linarith [le_max_left (0:ℝ) L], ?_⟩
    dsimp [coast]
    linarith [le_max_right (0:ℝ) L]

/-- This conservative formula fails the old 0.15 m reference-position test. -/
theorem old_contract_fails_simple_bound :
    (1/1000:ℝ) + travelBudget (41/100) (1/10) (1/20) (6/5) 8 = 4111/25600 ∧
    (3/20:ℝ) < (1/1000) + travelBudget (41/100) (1/10) (1/20) (6/5) 8 := by
  norm_num [travelBudget, velocityBudget]

end LeanControls.Recovery
