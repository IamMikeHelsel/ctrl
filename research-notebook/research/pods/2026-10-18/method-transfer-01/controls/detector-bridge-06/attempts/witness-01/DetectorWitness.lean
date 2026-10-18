module
public import DetectorSampling
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.DetectorWitness
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
    IsTrajectory (12/25) (fun _ => 8) (fun _ => -6/5) (fun s => state (1/20+s)) := by
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

open DetectorBridge DetectorSampling

theorem braking_example : BrakingExecution state (fun _ => 8) (fun _ => 1/10)
    (fun _ => 8) (fun _ => -6/5) := by
  refine ⟨restored_trajectory.1.continuousOn,restored_trajectory.2.1,
    continuousOn_const,?_,?_,?_,?_,?_,restored_trajectory.2.2,continuousOn_const,?_,?_⟩
  all_goals first | (intros; norm_num) | norm_num [state,lossState]

def readings (n : ℕ) : State := state (sample n)

theorem readings_valid : Readings state readings := by
  intro n hn
  norm_num [SensorBox,readings]

theorem nonvacuous_finite_detection :
    ∃ k : ℕ, k ≤ 1058 ∧ ClearancePolicy.Guard (readings k) ∧
      (∀ j < k, ¬ ClearancePolicy.Guard (readings j)) ∧
      ∀ D ∈ Icc (0:ℝ) (1/2000), sample k+D ≤ 53/100 :=
  finite_first_guard braking_example readings_valid

/-- C1 permits arbitrarily large negative acceleration. This exact flow
satisfies its physical contract and reaches zero during the loss phase,
but its exact acceleration reading fails the C5 guard. -/
def fast (t : ℝ) : State := heldSolution 8 t (-100) ![0,2/5,-100]

theorem c1_fast_counterexample :
    IsTrajectory (1/20) (fun _ => 8) (fun _ => -100) fast ∧
    IsTrajectory (479/1000) (fun _ => 8) (fun _ => -100) (fun s => fast (1/20+s)) ∧
    fast 0 0 ≤ 1/1000 ∧ 0 ≤ fast 0 1 ∧ fast 0 1 ≤ 41/100 ∧ fast 0 2 ≤ 1/10 ∧
    fast (1/250) 1=0 ∧ (∀ t ∈ Ico 0 (1/250), 0<fast t 1) ∧
    ¬ ClearancePolicy.Guard (fast (1/250)) := by
  refine ⟨ActualStop.constant_flow_isTrajectory (by norm_num) _ _ _,
    ActualStop.constant_flow_shift_isTrajectory (by norm_num) _ _ _ _,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | norm_num [fast,heldSolution,ClearancePolicy.Guard] | skip
  intro t ht
  norm_num [fast,heldSolution]
  linarith [ht.2]

/-- Positive acceleration at an initial zero defeats the acceleration guard.
This is a loss-prefix counterexample; its later recovered phase is not claimed here. -/
theorem zero_initial_prefix :
    IsTrajectory (1/20) (fun _ => 8) (fun _ => 1/10)
      (fun t => heldSolution 8 t (1/10) ![0,0,1/10]) ∧
    heldSolution 8 0 (1/10) ![0,0,1/10] 1=0 ∧
    ¬ ClearancePolicy.Guard (heldSolution 8 (1/1000) (1/10) ![0,0,1/10]) := by
  refine ⟨ActualStop.constant_flow_isTrajectory (by norm_num) _ _ _,?_,?_⟩ <;>
    norm_num [heldSolution,ClearancePolicy.Guard]

end LeanControls.DetectorWitness
