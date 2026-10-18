module
public import Recovery
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.Recovery.Witness
open Set Filter
open UncertainLag (State heldSolution)
open VariableResponse

/-- One second of exact coasting, then a negative effective target with unit
response rate. Position, velocity and acceleration agree at recovery. -/
def state (t : ℝ) : State :=
  if t ≤ 1 then coast t else heldSolution 1 (t-1) (-1) ![1,1,0]

theorem coast_then_brake_trajectory :
    Continuous state ∧ IsTrajectory 1 (fun _ => 1) (fun _ => 0) state ∧
    IsTrajectory 2 (fun _ => 1) (fun _ => -1) (fun s => state (1+s)) := by
  have hc : Continuous (fun t => heldSolution 1 (t-1) (-1) ![1,1,0]) := by
    have hh : Continuous (fun s => heldSolution 1 s (-1) ![1,1,0]) :=
      continuous_pi fun i => continuous_iff_continuousAt.mpr fun t =>
        (UncertainLag.exact_ode (by norm_num : (1:ℝ) ≠ 0) (-1) t ![1,1,0] i).continuousAt
    exact hh.comp (continuous_id.sub continuous_const)
  have hstate : Continuous state := by
    refine Continuous.if_le (continuous_pi fun i => by fin_cases i <;> simp [coast] <;> fun_prop)
      hc continuous_id continuous_const ?_
    intro t ht
    simp [ht, coast, UncertainLag.exact_initial]
  refine ⟨hstate, ?_, ?_⟩
  · refine ⟨hstate.continuousOn, ?_⟩
    intro t ht i
    have hd := (no_recovery_counterexample.1 1).ode t ht i
    have he : state t = coast t := by simp [state, ht.2.le]
    rw [he]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    simp [state, hs.le]
  · refine ⟨(hstate.comp (continuous_const.add continuous_id)).continuousOn, ?_⟩
    intro s hs i
    have he : state (1+s) = heldSolution 1 s (-1) ![1,1,0] := by
      simp [state, show ¬ 1+s ≤ 1 by linarith [hs.1]]
    rw [he]
    apply (UncertainLag.exact_ode (by norm_num : (1:ℝ) ≠ 0) (-1) s ![1,1,0] i).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs.1] with u hu
    change 0 < u at hu
    simp [state, show ¬ 1+u ≤ 1 by linarith, not_le_of_gt hu]

/-- This instance actually loses all effective braking for one second. It is
not the faster immediate-braking example from the earlier delayed-stop work. -/
theorem coast_then_brake_first_zero :
    ∃ τ ∈ Icc (0:ℝ) 3, state τ 1 = 0 ∧
      (∀ t ∈ Ico 0 τ, 0 < state t 1) ∧
      ∀ t ∈ Icc 0 τ, state t 0 ≤ 3 := by
  have h := restored_braking_first_zero (X := 0) (v0 := 1) (A := 0) (T := 1)
    (b := 1) (k := 1) (f := state)
    (rLoss := fun _ => 1) (qLoss := fun _ => 0)
    (rBrake := fun _ => 1) (qBrake := fun _ => -1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    coast_then_brake_trajectory.1.continuousOn
    coast_then_brake_trajectory.2.1 continuousOn_const
    (by intros; norm_num) (by intros; norm_num)
    (by norm_num [state, coast]) (by norm_num [state, coast])
    (by norm_num [state, coast]) (by norm_num [state, coast])
    (by convert coast_then_brake_trajectory.2.2 using 1 <;> norm_num [recoveryHorizon, velocityBudget])
    continuousOn_const (by intros; norm_num) (by intros; norm_num)
  norm_num [recoveryHorizon, travelBudget, velocityBudget] at h ⊢
  exact h

end LeanControls.Recovery.Witness
