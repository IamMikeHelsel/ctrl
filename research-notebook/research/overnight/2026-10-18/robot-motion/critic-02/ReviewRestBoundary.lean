import ReviewWitnesses
open Set
noncomputable section
namespace IndependentMotionReview02
open RobotMotion RobotMotion.AccelerationAdmission
open LeanControls LeanControls.UncertainLag LeanControls.VariableResponse
open LeanControls.RobustHold LeanControls.TrackingReplan LeanControls.ScaledTracking

def drift (t : ℝ) : State := ![q t 0 + t/1000000, q t 1 + 1/1000000, q t 2]
def driftDisturbance (t : ℝ) : ℝ := (800*t+60)/1000000

theorem drift_actual_trajectory : IsTrajectory (5/2) (fun _ => 96)
    (fun t => physicalInput 10 drift q j t + driftDisturbance t) drift := by
  constructor
  · apply continuousOn_pi.mpr
    intro i
    have hc := referenceState_continuous 0 (1/5) (realEvents deferredReturn)
    fin_cases i
    · convert (((continuous_apply 0).comp hc).add (continuous_id.div_const 1000000)).continuousOn using 1
      funext t
      simp [drift,q,Function.comp_def]
    · convert (((continuous_apply 1).comp hc).add (continuous_const : Continuous (fun _ : ℝ => (1/1000000:ℝ)))).continuousOn using 1
      funext t
      simp [drift,q,Function.comp_def]
    · simpa [drift,q,Function.comp_def] using ((continuous_apply 2).comp hc).continuousOn
  · intro t ht i
    have hd := referenceState_deriv (h:=1/5) (by norm_num) 0 (realEvents deferredReturn) t i
    fin_cases i
    · convert hd.add ((hasDerivAt_id t).div_const 1000000) using 1 <;> simp [drift,q]
      funext s
      rfl
    · convert hd.add_const (1/1000000) using 1 <;> simp [drift,q]
    · convert hd using 1 <;> simp [drift,q,j,physicalInput,driftDisturbance] <;> ring

theorem drift_disturbance_bound : ∀ t ∈ Icc (0:ℝ) (5/2), |driftDisturbance t| ≤ 1/100 := by
  intro t ht
  apply abs_le.mpr
  dsimp [driftDisturbance]
  constructor <;> linarith [ht.1,ht.2]

theorem drift_initial_cube : ∀ i, |coordinates 0 (scaledError 10 drift q 0) i| ≤ 1/5000 := by
  intro i
  fin_cases i <;> norm_num [coordinates,scaledError,scaleState,error,drift]

theorem actual_terminal_velocity_not_zero : drift (17/10) 1 = 1/1000000 := by
  have hv := (deferred_return_reference_contract.2.2.2 (17/10) (by norm_num)).2.1
  change velocity (1/5) (realEvents deferredReturn) (17/10) + 1/1000000 = 1/1000000
  rw [hv,zero_add]

theorem drift_actual_arrival :
    ∀ t ∈ Icc (71/50:ℝ) (5/2), |drift t 0| ≤ 1/5000 := by
  have proof := delayed_return_physical_position
    (f:=drift) (r:=fun _ => 96) (w:=driftDisturbance)
    (by simpa [q,j] using drift_actual_trajectory)
    (by intro t ht; norm_num) (by intro t ht; norm_num)
    drift_disturbance_bound (by simpa [q] using drift_initial_cube)
  exact proof.2.2.1

end IndependentMotionReview02
