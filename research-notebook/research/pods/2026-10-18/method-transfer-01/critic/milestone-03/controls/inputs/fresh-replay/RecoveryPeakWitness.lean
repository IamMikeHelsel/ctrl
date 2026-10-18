module
public import RecoveryPeak
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.RecoveryPeak.Witness
open Set Filter
open UncertainLag (State heldSolution)
open VariableResponse

def lossState (t : ℝ) : State :=
  ![1/1000+(41/100)*t+(1/10)*t^2/2,41/100+(1/10)*t,1/10]

/-- The effective target changes from +0.1 to -1.2 at 0.05 s. The actual
position, velocity and acceleration are continuous across that change. -/
def state (t : ℝ) : State :=
  if t ≤ 1/20 then lossState t
  else heldSolution 8 (t-1/20) (-6/5) StoppingCertificate.engagementUpper

theorem loss_trajectory : IsTrajectory (1/20) (fun _ => 8) (fun _ => 1/10) lossState := by
  constructor
  · exact (continuous_pi fun i => by fin_cases i <;> simp [lossState] <;> fun_prop).continuousOn
  · intro t ht i
    fin_cases i
    · convert (((hasDerivAt_id t).const_mul (41/100:ℝ)).const_add (1/1000)).add
        ((((hasDerivAt_id t).pow 2).const_mul (1/10:ℝ)).div_const 2) using 1
      · funext s
        simp [lossState]
      · simp [lossState]
        ring
    · simpa [lossState] using ((hasDerivAt_id t).const_mul (1/10:ℝ)).const_add (41/100)
    · simpa [lossState] using hasDerivAt_const t (1/10:ℝ)

theorem restored_trajectory :
    Continuous state ∧ IsTrajectory (1/20) (fun _ => 8) (fun _ => 1/10) state ∧
    IsTrajectory (479/1000) (fun _ => 8) (fun _ => -6/5) (fun s => state (1/20+s)) := by
  have hc : Continuous (fun t => heldSolution 8 (t-1/20) (-6/5)
      StoppingCertificate.engagementUpper) := by
    have hh : Continuous (fun s => heldSolution 8 s (-6/5)
        StoppingCertificate.engagementUpper) :=
      continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
        (UncertainLag.exact_ode (by norm_num : (8:ℝ) ≠ 0) (-6/5) t
          StoppingCertificate.engagementUpper i).continuousAt
    exact hh.comp (continuous_id.sub continuous_const)
  have hstate : Continuous state := by
    refine Continuous.if_le (continuous_pi fun i => by fin_cases i <;>
      simp [lossState] <;> fun_prop) hc continuous_id continuous_const ?_
    intro t ht
    simp [ht,lossState,UncertainLag.exact_initial,StoppingCertificate.engagementUpper]
    norm_num
  refine ⟨hstate,?_,?_⟩
  · refine ⟨hstate.continuousOn,?_⟩
    intro t ht i
    have hd := loss_trajectory.ode t ht i
    have he : state t = lossState t := by rw [state,if_pos ht.2.le]
    rw [he]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    rw [state,if_pos hs.le]
  · refine ⟨(hstate.comp (continuous_const.add continuous_id)).continuousOn,?_⟩
    intro s hs i
    have he : state (1/20+s) = heldSolution 8 s (-6/5)
        StoppingCertificate.engagementUpper := by
      rw [state,if_neg (show ¬ (1/20:ℝ)+s ≤ 1/20 by linarith [hs.1])]
      simp only [add_sub_cancel_left]
    rw [he]
    apply (UncertainLag.exact_ode (by norm_num : (8:ℝ) ≠ 0) (-6/5) s
      StoppingCertificate.engagementUpper i).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs.1] with u hu
    change 0 < u at hu
    rw [state,if_neg (show ¬ (1/20:ℝ)+u ≤ 1/20 by linarith)]
    simp only [add_sub_cancel_left]

theorem restored_first_zero :
    ∃ τ ∈ Icc (0:ℝ) (529/1000), state τ 1 = 0 ∧
      (∀ t ∈ Ico 0 τ, 0 < state t 1) ∧
      ∀ t ∈ Icc 0 τ, state t 0 ≤ 71/500 := by
  exact old_contract_first_zero restored_trajectory.1.continuousOn
    restored_trajectory.2.1 continuousOn_const
    (by intros; norm_num) (by intros; norm_num)
    (by norm_num [state,lossState]) (by norm_num [state,lossState])
    (by norm_num [state,lossState]) (by norm_num [state,lossState])
    restored_trajectory.2.2 continuousOn_const
    (by intros; norm_num) (by intros; norm_num)

/-- Zero initial speed can be followed by positive motion under a lagged
negative target. A first-zero conclusion alone is not maintained rest. -/
theorem zero_speed_not_hold :
    heldSolution 1 0 (-1) ![0,0,1] 1 = 0 ∧
    0 < heldSolution 1 1 (-1) ![0,0,1] 1 ∧
    heldSolution 1 3 (-1) ![0,0,1] 1 < 0 := by
  have hp := mul_lt_mul_of_pos_left Real.exp_one_gt_two (Real.exp_pos (-1:ℝ))
  have hid : Real.exp (-1:ℝ)*Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  rw [hid] at hp
  have he := Real.exp_pos (-3:ℝ)
  norm_num [heldSolution]
  constructor <;> linarith

end LeanControls.RecoveryPeak.Witness
