import DetectorWitness
noncomputable section
namespace DetectorReview
open Set
open LeanControls
open UncertainLag (State heldSolution)
open VariableResponse DetectorBridge DetectorSampling

def earlyState (t : ℝ) : State := heldSolution 8 t (-6/5) ![1/1000,39/100,-6/5]

theorem early_execution : BrakingExecution earlyState (fun _ => 8) (fun _ => -6/5)
    (fun _ => 8) (fun _ => -6/5) := by
  have hc : Continuous earlyState :=
    continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
      (UncertainLag.exact_ode (by norm_num : (8:ℝ) ≠ 0) (-6/5) t
        ![1/1000,39/100,-6/5] i).continuousAt
  refine ⟨hc.continuousOn,
    ActualStop.constant_flow_isTrajectory (by norm_num) _ _ _,
    continuousOn_const, ?_, ?_, ?_, ?_, ?_,
    ActualStop.constant_flow_shift_isTrajectory (by norm_num) _ _ _ _,
    continuousOn_const, ?_, ?_⟩
  all_goals norm_num [earlyState,heldSolution]

/-- Full C6-family witness: a valid exact reading can qualify before zero. -/
theorem guard_before_zero :
    sample 640 = (8/25:ℝ) ∧ ClearancePolicy.Guard (earlyState (8/25)) ∧
    earlyState (8/25) 1 = 3/500 ∧ (8/25:ℝ) < 13/40 ∧
    earlyState (13/40) 1 = 0 ∧
    (∀ t ∈ Ico (0:ℝ) (13/40), 0 < earlyState t 1) := by
  refine ⟨by norm_num [sample], ?_, ?_, by norm_num, ?_, ?_⟩
  · norm_num [ClearancePolicy.Guard,earlyState,heldSolution]
  · norm_num [earlyState,heldSolution]
  · norm_num [earlyState,heldSolution]
  · intro t ht
    norm_num [earlyState,heldSolution]
    linarith [ht.2]

theorem guard_time_lower {f : ℝ → State} {rL qL rB qB : ℝ → ℝ}
    (ex : BrakingExecution f rL qL rB qB) {t : ℝ} {m : State}
    (ht : t ∈ Icc (0:ℝ) (53/100)) (hm : SensorBox (f t) m)
    (hg : ClearancePolicy.Guard m) : (18439/61000:ℝ) ≤ t := by
  have hv := all_velocity_lower ex t ht
  have he := abs_le.mp hm.2.1
  have hmv := abs_le.mp hg.2.1
  linarith

end DetectorReview
#print axioms DetectorReview.early_execution
#print axioms DetectorReview.guard_before_zero
#print axioms DetectorReview.guard_time_lower
