module
public import ActualStop
@[expose] public section
noncomputable section
namespace LeanControls.ReleaseCounterexample
open Set UncertainLag VariableResponse

/-- Zero target after a true stop is a valid lagged-axis trajectory. Residual
negative acceleration decays, but it creates a nonzero backward velocity. -/
theorem release_is_trajectory (H : ℝ) :
    IsTrajectory H (fun _ => 8) (fun _ => 0)
      (fun t => heldSolution 8 t 0 ![0,0,-1]) :=
  ActualStop.constant_flow_isTrajectory (by norm_num) H 0 ![0,0,-1]

/-- Even with exactly zero initial velocity, release to target zero eventually
crosses any finite rear position limit. No measurement error is needed. -/
theorem zero_velocity_release_drifts (L : ℝ) (hL : 0 ≤ L) :
    heldSolution 8 0 0 ![0,0,-1] 1 = 0 ∧
    ∃ t : ℝ, 0 ≤ t ∧ heldSolution 8 t 0 ![0,0,-1] 0 < -L := by
  constructor
  · norm_num [exact_initial]
  · refine ⟨8*(L+1), by positivity, ?_⟩
    have he := Real.exp_nonneg (-(8*(8*(L+1))))
    norm_num [heldSolution]
    nlinarith

end LeanControls.ReleaseCounterexample
