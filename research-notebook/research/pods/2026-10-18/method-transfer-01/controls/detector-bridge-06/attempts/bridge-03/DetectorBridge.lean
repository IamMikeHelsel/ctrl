module
public import RecoveryPeak
public import ClearancePolicy
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.DetectorBridge
open Set Filter
open UncertainLag (State heldSolution)
open VariableResponse

/-- A supplied continued-braking state, not an actual switched execution.
The lower bounds and rate ceiling are explicit additions to C1. -/
structure BrakingExecution (f : ℝ → State) (rLoss qLoss rBrake qBrake : ℝ → ℝ) : Prop where
  continuous : ContinuousOn f (Icc 0 (53/100))
  loss : IsTrajectory (1/20) rLoss qLoss f
  loss_rate_continuous : ContinuousOn rLoss (Icc 0 (1/20))
  loss_rate : ∀ t ∈ Icc 0 (1/20), 0 ≤ rLoss t
  loss_target : ∀ t ∈ Icc 0 (1/20), -61/50 ≤ qLoss t ∧ qLoss t ≤ 1/10
  position_initial : f 0 0 ≤ 1/1000
  velocity_initial : 39/100 ≤ f 0 1 ∧ f 0 1 ≤ 41/100
  acceleration_initial : -61/50 ≤ f 0 2 ∧ f 0 2 ≤ 1/10
  brake : IsTrajectory (12/25) rBrake qBrake (fun s => f (1/20+s))
  brake_rate_continuous : ContinuousOn rBrake (Icc 0 (12/25))
  brake_rate : ∀ s ∈ Icc 0 (12/25), 8 ≤ rBrake s ∧ rBrake s ≤ 12
  brake_target : ∀ s ∈ Icc 0 (12/25), -61/50 ≤ qBrake s ∧ qBrake s ≤ -6/5

theorem trajectory_restrict {H S : ℝ} {r q : ℝ → ℝ} {f : ℝ → State}
    (hf : IsTrajectory H r q f) (hS : S ≤ H) : IsTrajectory S r q f := by
  exact ⟨hf.continuous.mono (Icc_subset_Icc_right hS), fun t ht i => hf.ode t ⟨ht.1,ht.2.trans_le hS⟩ i⟩

theorem acceleration_lower {H L : ℝ} (hH : 0 ≤ H)
    {r q : ℝ → ℝ} {f : ℝ → State}
    (hrc : ContinuousOn r (Icc 0 H)) (hr : ∀ t ∈ Icc 0 H, 0 ≤ r t)
    (hq : ∀ t ∈ Icc 0 H, L ≤ q t) (hf : IsTrajectory H r q f) (ha : L ≤ f 0 2) :
    ∀ t ∈ Icc 0 H, L ≤ f t 2 := by
  apply linear_comparison hH hrc continuousOn_const
    ((continuous_apply 2).comp_continuousOn hf.continuous)
    (fun t _ => hasDerivAt_const t L) (fun t ht => hf.ode t ht 2) ha
  intro t ht
  have hp := mul_nonpos_of_nonneg_of_nonpos (hr t ⟨ht.1.le,ht.2.le⟩)
    (show L-q t ≤ 0 by linarith [hq t ⟨ht.1.le,ht.2.le⟩])
  change 0-r t*(q t-f t 2)+r t*(L-f t 2) ≤ 0
  nlinarith

theorem velocity_lower {H L U : ℝ} (hH : 0 ≤ H)
    {r q : ℝ → ℝ} {f : ℝ → State} (hf : IsTrajectory H r q f)
    (hi : U ≤ f 0 1) (ha : ∀ t ∈ Icc 0 H, L ≤ f t 2) :
    ∀ t ∈ Icc 0 H, U+L*t ≤ f t 1 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => U+L*s) L t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul L).const_add U
  exact derivative_comparison hH (by fun_prop)
    ((continuous_apply 1).comp_continuousOn hf.continuous)
    (fun t _ => hd t) (fun t ht => hf.ode t ht 1) (by simpa using hi)
    (fun t ht => ha t ⟨ht.1.le,ht.2.le⟩)

variable {f : ℝ → State} {rLoss qLoss rBrake qBrake : ℝ → ℝ}
variable (ex : BrakingExecution f rLoss qLoss rBrake qBrake)
include ex

theorem all_acceleration_lower : ∀ t ∈ Icc 0 (53/100), -61/50 ≤ f t 2 := by
  have hL := acceleration_lower (by norm_num : (0:ℝ) ≤ 1/20)
    ex.loss_rate_continuous ex.loss_rate (fun t ht => (ex.loss_target t ht).1) ex.loss ex.acceleration_initial.1
  have hB := acceleration_lower (by norm_num : (0:ℝ) ≤ 12/25)
    ex.brake_rate_continuous (fun t ht => by linarith [(ex.brake_rate t ht).1])
    (fun t ht => (ex.brake_target t ht).1) ex.brake
    (by simpa using hL (1/20) ⟨by norm_num,le_rfl⟩)
  intro t ht
  by_cases hp : t ≤ 1/20
  · exact hL t ⟨ht.1,hp⟩
  · have hh := hB (t-1/20) ⟨by linarith,by linarith [ht.2]⟩
    simpa only [add_sub_cancel] using hh

theorem all_velocity_lower : ∀ t ∈ Icc 0 (53/100), 39/100-(61/50)*t ≤ f t 1 := by
  have ha := all_acceleration_lower ex
  have hL := velocity_lower (by norm_num : (0:ℝ) ≤ 1/20) ex.loss ex.velocity_initial.1
    (fun t ht => ha t ⟨ht.1,by linarith [ht.2]⟩)
  have hB := velocity_lower (L := -61/50) (U := 39/100-(61/50)*(1/20))
    (by norm_num : (0:ℝ) ≤ 12/25) ex.brake
    (by have hh := hL (1/20) ⟨by norm_num,le_rfl⟩; dsimp at hh ⊢; linarith)
    (fun s hs => ha (1/20+s) ⟨by linarith [hs.1],by linarith [hs.2]⟩)
  intro t ht
  by_cases hp : t ≤ 1/20
  · have hh := hL t ⟨ht.1,hp⟩; linarith
  · have hh := hB (t-1/20) ⟨by linarith,by linarith [ht.2]⟩
    simp only [add_sub_cancel] at hh
    linarith

theorem recovered_upper : ∀ s ∈ Icc 0 (12/25), ∀ i : Fin 3,
    f (1/20+s) i ≤ heldSolution 8 s (-6/5) StoppingCertificate.engagementUpper i := by
  have ha := Recovery.loss_acceleration_upper (by norm_num : (0:ℝ) ≤ 1/20)
    ex.loss_rate_continuous ex.loss_rate (fun t ht => (ex.loss_target t ht).2) ex.loss ex.acceleration_initial.2
  have hd : ActualStop.IsDelayTrajectory (1/20) f :=
    ⟨ex.loss.continuous,(fun t ht => ex.loss.ode t ht 0),(fun t ht => ex.loss.ode t ht 1)⟩
  have hp := ActualStop.delay_coordinate_upper (by norm_num : (0:ℝ) ≤ 1/20)
    hd ex.position_initial ex.velocity_initial.2 ha
  have he := hp (1/20) ⟨by norm_num,le_rfl⟩
  have hi : ∀ i : Fin 3, f (1/20) i ≤ StoppingCertificate.engagementUpper i := by
    intro i
    fin_cases i <;> norm_num [StoppingCertificate.engagementUpper] <;>
      linarith [ha (1/20) ⟨by norm_num,le_rfl⟩]
  simpa only [neg_div] using Recovery.recovered_upper_flow (b := 6/5)
    (by norm_num : (0:ℝ) ≤ 12/25) (by norm_num : (0:ℝ)<8)
    ex.brake_rate_continuous (fun s hs => (ex.brake_rate s hs).1)
    (fun s hs => by simpa only [neg_div] using (ex.brake_target s hs).2) ex.brake
    (by norm_num [StoppingCertificate.engagementUpper]) (by simpa using hi)

theorem all_position_upper : ∀ t ∈ Icc 0 (53/100), f t 0 ≤ 71/500 := by
  have ha := Recovery.loss_acceleration_upper (by norm_num : (0:ℝ) ≤ 1/20)
    ex.loss_rate_continuous ex.loss_rate (fun t ht => (ex.loss_target t ht).2) ex.loss ex.acceleration_initial.2
  have hd : ActualStop.IsDelayTrajectory (1/20) f :=
    ⟨ex.loss.continuous,(fun t ht => ex.loss.ode t ht 0),(fun t ht => ex.loss.ode t ht 1)⟩
  have hp := ActualStop.delay_coordinate_upper (by norm_num : (0:ℝ) ≤ 1/20)
    hd ex.position_initial ex.velocity_initial.2 ha
  intro t ht
  by_cases hpre : t ≤ 1/20
  · have hh := (hp t ⟨ht.1,hpre⟩).1
    have hsq : t^2 ≤ (1/20:ℝ)^2 := by nlinarith [ht.1]
    nlinarith
  · have hs : t-1/20 ∈ Icc (0:ℝ) (12/25) := ⟨by linarith,by linarith [ht.2]⟩
    have hh := (recovered_upper ex (t-1/20) hs 0).trans (RecoveryPeak.old_upper_position_le hs.1)
    simpa only [add_sub_cancel] using hh

theorem late_acceleration_upper : ∀ t ∈ Icc (1/10) (53/100), f t 2 ≤ -19/70 := by
  have he : Real.exp (-(2/5:ℝ)) ≤ 5/7 := by
    have hh := Real.add_one_le_exp (2/5:ℝ)
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (-(2/5:ℝ)))
    have hi : Real.exp (-(2/5:ℝ))*Real.exp (2/5)=1 := by rw [← Real.exp_add]; norm_num
    rw [hi] at hm
    linarith
  intro t ht
  have hs : t-1/20 ∈ Icc (0:ℝ) (12/25) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hh := recovered_upper ex (t-1/20) hs 2
  have hx : Real.exp (-8*(t-1/20)) ≤ 5/7 :=
    (Real.exp_le_exp.mpr (by linarith [ht.1])).trans he
  norm_num [heldSolution,StoppingCertificate.engagementUpper] at hh
  nlinarith

theorem first_zero : ∃ τ ∈ Icc (39/122:ℝ) (529/1000),
    f τ 1=0 ∧ (∀ t ∈ Ico 0 τ, 0 < f t 1) := by
  have hs : (479/1000:ℝ) ≤ 12/25 := by norm_num
  obtain ⟨τ,hτ,hz,hbefore,_⟩ := RecoveryPeak.old_contract_first_zero
    (ex.continuous.mono (Icc_subset_Icc_right (by norm_num))) ex.loss
    ex.loss_rate_continuous ex.loss_rate (fun t ht => (ex.loss_target t ht).2)
    ex.position_initial (by linarith [ex.velocity_initial.1]) ex.velocity_initial.2 ex.acceleration_initial.2
    (trajectory_restrict ex.brake hs) (ex.brake_rate_continuous.mono (Icc_subset_Icc_right hs))
    (fun t ht => (ex.brake_rate t ⟨ht.1,ht.2.trans hs⟩).1)
    (fun t ht => (ex.brake_target t ⟨ht.1,ht.2.trans hs⟩).2)
  have hl := all_velocity_lower ex τ ⟨hτ.1,by linarith [hτ.2]⟩
  exact ⟨τ,⟨by rw [hz] at hl; linarith,hτ.2⟩,hz,hbefore⟩

end LeanControls.DetectorBridge
