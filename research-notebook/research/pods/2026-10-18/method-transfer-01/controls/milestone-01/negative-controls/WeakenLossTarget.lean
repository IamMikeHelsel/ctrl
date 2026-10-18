module
public import Recovery
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! A full-time peak certificate for the unchanged restored-effective-braking
model. A supplied continuous physical state spans both phases. The analytical
certificate bounds an explicit upper flow, not the physical trajectory as a
premise. No upper response-rate bound or general existence claim is added. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.RecoveryPeak
open Set
open UncertainLag (State heldSolution)
open VariableResponse Recovery

/-- A pure upper-flow certificate transfers to one physical first-zero prefix.
The analytical inputs hEnd/hPeak concern only the explicit constant upper flow.
They do not assume any terminal or whole-path bound on the physical state. -/
theorem first_zero_of_envelope_certificate {X v0 A T b k S B : ℝ}
    (hv0 : 0 ≤ v0) (hA : 0 ≤ A) (hT : 0 ≤ T) (hb : 0 < b) (hk : 0 < k)
    (hS : 0 ≤ S)
    (hEnd : heldSolution k S (-b) ![X+v0*T+A*T^2/2,v0+A*T,A] 1 ≤ 0)
    (hPeak : ∀ s ∈ Icc 0 S,
      heldSolution k s (-b) ![X+v0*T+A*T^2/2,v0+A*T,A] 0 ≤ B)
    {f : ℝ → State} {rLoss qLoss rBrake qBrake : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 (T+S)))
    (hLoss : IsTrajectory T rLoss qLoss f)
    (hrLossC : ContinuousOn rLoss (Icc 0 T))
    (hrLoss : ∀ t ∈ Icc 0 T, 0 ≤ rLoss t)
    (hqLoss : ∀ t ∈ Icc 0 T, qLoss t ≤ A+1)
    (hx : f 0 0 ≤ X) (hv : 0 ≤ f 0 1) (hvHi : f 0 1 ≤ v0) (ha : f 0 2 ≤ A)
    (hBrake : IsTrajectory S rBrake qBrake (fun s => f (T+s)))
    (hrBrakeC : ContinuousOn rBrake (Icc 0 S))
    (hrBrake : ∀ s ∈ Icc 0 S, k ≤ rBrake s)
    (hqBrake : ∀ s ∈ Icc 0 S, qBrake s ≤ -b) :
    ∃ τ ∈ Icc 0 (T+S), f τ 1 = 0 ∧ (∀ t ∈ Ico 0 τ, 0 < f t 1) ∧
      ∀ t ∈ Icc 0 τ, f t 0 ≤ B := by
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
  have hvend : f (T+S) 1 ≤ 0 := (hflow S ⟨hS,le_rfl⟩ 1).trans hEnd
  have hP : X+v0*T+A*T^2/2 ≤ B := by
    simpa only [UncertainLag.exact_initial, Matrix.cons_val_zero] using hPeak 0 ⟨le_rfl,hS⟩
  have hpath : ∀ t ∈ Icc 0 (T+S), f t 0 ≤ B := by
    intro t ht
    by_cases hpre : t ≤ T
    · have hp := (hprefix t ⟨ht.1,hpre⟩).1
      have hlin := mul_le_mul_of_nonneg_left hpre hv0
      have hsq : t^2 ≤ T^2 := by nlinarith [ht.1]
      have hquad := mul_le_mul_of_nonneg_left hsq hA
      linarith
    · have hs : t-T ∈ Icc 0 S := ⟨by linarith,by linarith [ht.2]⟩
      have hh := (hflow (t-T) hs 0).trans (hPeak (t-T) hs)
      simpa only [add_sub_cancel] using hh
  exact FirstStop.first_zero_with_travel_bound (add_nonneg hT hS)
    ((continuous_apply 1).comp_continuousOn hfc) hv hvend hpath

theorem exp_neg_62_25_le : Real.exp (-(62/25:ℝ)) ≤ 21/250 := by
  have hp := Real.sum_le_exp_of_nonneg (show 0 ≤ (62/25:ℝ) by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-(62/25:ℝ)))
  have he : Real.exp (-(62/25:ℝ)) * Real.exp (62/25:ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith

/-- Three time intervals keep the negative exponential transient. The bound
holds for all nonnegative times of the upper flow, not only its endpoint. -/
theorem old_upper_position_le {t : ℝ} (ht : 0 ≤ t) :
    heldSolution 8 t (-6/5) StoppingCertificate.engagementUpper 0 ≤ 71/500 := by
  have he0 := Real.exp_nonneg (-8*t)
  have he1 : Real.exp (-(8*t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hearly : t ≤ 1/5
  · norm_num [heldSolution, StoppingCertificate.engagementUpper]
    nlinarith [sq_nonneg t]
  · have he21 : Real.exp (-(8*t)) ≤ 21/100 :=
      (Real.exp_le_exp.mpr (show -(8*t) ≤ -(8/5:ℝ) by linarith)).trans
        StoppingCertificate.exp_neg_eight_fifths_le
    by_cases hmid : t ≤ 31/100
    · have hm := mul_nonneg (show 0 ≤ (31/100:ℝ)-t by linarith)
        (show 0 ≤ (231/400:ℝ)-(3/5)*(t+31/100) by linarith)
      norm_num [heldSolution, StoppingCertificate.engagementUpper]
      nlinarith
    · have he : Real.exp (-(8*t)) ≤ 21/250 :=
        (Real.exp_le_exp.mpr (show -(8*t) ≤ -(62/25:ℝ) by linarith)).trans
          exp_neg_62_25_le
      norm_num [heldSolution, StoppingCertificate.engagementUpper]
      nlinarith [sq_nonneg (t-(77/160:ℝ))]

theorem exp_neg_four_lower : (256/14641:ℝ) ≤ Real.exp (-4) := by
  have he : Real.exp (1:ℝ) ≤ 11/4 := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_nonneg (1:ℝ)) he 4
  have hfour : Real.exp (4:ℝ) ≤ (11/4:ℝ)^4 := by
    simpa using (show Real.exp (1:ℝ)^4 ≤ (11/4:ℝ)^4 from hp)
  have hm := mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg (-4:ℝ))
  have hid : Real.exp (-4:ℝ)*Real.exp 4 = 1 := by
    rw [← Real.exp_add]; norm_num
  rw [hid] at hm
  norm_num at hm
  linarith

theorem old_upper_velocity_negative :
    heldSolution 8 (479/1000) (-6/5) StoppingCertificate.engagementUpper 1 < 0 := by
  have he : (256/14641:ℝ) ≤ Real.exp (-(8*(479/1000:ℝ))) :=
    exp_neg_four_lower.trans (Real.exp_le_exp.mpr (by norm_num))
  norm_num [heldSolution, StoppingCertificate.engagementUpper]
  norm_num at he
  linarith

/-- The old illustrative numerical contract now has a 0.142 m peak bound
and a 0.529 s first-zero deadline, with no upper response-rate bound.
The recovered target/rate premises persist through all 0.479 s after recovery.
The physical acceleration bound before recovery is derived from its ODE. -/
theorem old_contract_first_zero
    {f : ℝ → State} {rLoss qLoss rBrake qBrake : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 (529/1000)))
    (hLoss : IsTrajectory (1/20) rLoss qLoss f)
    (hrLossC : ContinuousOn rLoss (Icc 0 (1/20)))
    (hrLoss : ∀ t ∈ Icc 0 (1/20), 0 ≤ rLoss t)
    (hqLoss : ∀ t ∈ Icc 0 (1/20), qLoss t ≤ 1/10)
    (hx : f 0 0 ≤ 1/1000) (hv : 0 ≤ f 0 1)
    (hvHi : f 0 1 ≤ 41/100) (ha : f 0 2 ≤ 1/10)
    (hBrake : IsTrajectory (479/1000) rBrake qBrake (fun s => f (1/20+s)))
    (hrBrakeC : ContinuousOn rBrake (Icc 0 (479/1000)))
    (hrBrake : ∀ s ∈ Icc 0 (479/1000), 8 ≤ rBrake s)
    (hqBrake : ∀ s ∈ Icc 0 (479/1000), qBrake s ≤ -6/5) :
    ∃ τ ∈ Icc 0 (529/1000), f τ 1 = 0 ∧ (∀ t ∈ Ico 0 τ, 0 < f t 1) ∧
      ∀ t ∈ Icc 0 τ, f t 0 ≤ 71/500 := by
  have htime : (1/20:ℝ)+(479/1000)=529/1000 := by norm_num
  have hc : ContinuousOn f (Icc 0 ((1/20)+(479/1000))) := by
    convert hfc using 1 <;> norm_num
  have hend : heldSolution 8 (479/1000) (-(6/5))
      ![(1/1000)+(41/100)*(1/20)+(1/10)*(1/20)^2/2,
        (41/100)+(1/10)*(1/20),1/10] 1 ≤ 0 := by
    convert old_upper_velocity_negative.le using 1 <;>
      norm_num [StoppingCertificate.engagementUpper]
  have hpeak : ∀ s ∈ Icc 0 (479/1000), heldSolution 8 s (-(6/5))
      ![(1/1000)+(41/100)*(1/20)+(1/10)*(1/20)^2/2,
        (41/100)+(1/10)*(1/20),1/10] 0 ≤ 71/500 := by
    intro s hs
    convert old_upper_position_le hs.1 using 1 <;>
      norm_num [StoppingCertificate.engagementUpper]
  have hh := first_zero_of_envelope_certificate
    (X := 1/1000) (v0 := 41/100) (A := 1/10) (T := 1/20)
    (b := 6/5) (k := 8) (S := 479/1000) (B := 71/500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hend hpeak hc hLoss hrLossC hrLoss hqLoss hx hv hvHi ha
    hBrake hrBrakeC hrBrake (by
      intro s hs
      have h := hqBrake s hs
      norm_num at h ⊢
      exact h)
  simpa only [htime] using hh

/-- If the actual initial velocity is zero, it is already a first zero.
This also covers a positive acceleration upper bound: no unique nonnegative
zero of the comparison velocity is asserted. -/
theorem initially_zero_first_zero {H B : ℝ} (hH : 0 ≤ H) {f : ℝ → State}
    (hv : f 0 1 = 0) (hx : f 0 0 ≤ B) :
    ∃ τ ∈ Icc 0 H, f τ 1 = 0 ∧ (∀ t ∈ Ico 0 τ, 0 < f t 1) ∧
      ∀ t ∈ Icc 0 τ, f t 0 ≤ B := by
  refine ⟨0,⟨le_rfl,hH⟩,hv,?_,?_⟩
  · intro t ht
    exact False.elim (not_lt_of_ge ht.1 ht.2)
  · intro t ht
    have he : t=0 := le_antisymm ht.2 ht.1
    simpa [he] using hx

/-- Exact improvement on the same numerical inputs. The old simple budget
still fails 0.15 m. The new full-time envelope certificate passes it. -/
theorem old_certificate_comparison :
    (71/500:ℝ) < 3/20 ∧
    (3/20:ℝ) < (1/1000)+travelBudget (41/100) (1/10) (1/20) (6/5) 8 := by
  exact ⟨by norm_num,old_contract_fails_simple_bound.2⟩

/-- A concrete point of the exact upper flow rules out a 0.14 m certificate
for that flow. This is exact algebra, not a floating-point peak estimate. -/
theorem old_upper_exceeds_14cm :
    (7/50:ℝ) < heldSolution 8 (12/25) (-6/5) StoppingCertificate.engagementUpper 0 := by
  have he := Real.exp_pos (-(8*(12/25:ℝ)))
  norm_num [heldSolution, StoppingCertificate.engagementUpper]
  norm_num at he
  linarith

end LeanControls.RecoveryPeak
