module
public import LeanControls.TravelSafety

/-! Checked boundary of interpretation: a position-only initial condition does
not suffice for the same saturated lag plant and timing interval. -/
@[expose] public section
noncomputable section
namespace LeanControls.TravelScope
open SaturatedLag

def unsafeInitial : State := ![19/10,1,0]

theorem position_only_initial : |unsafeInitial 0| < 2 ∧
    RobustPD.saturate 1 (input unsafeInitial) = -1 := by
  norm_num [unsafeInitial, input, RobustPD.saturate]

/-- At an admitted elapsed time, a state initially within the position limit
escapes under the same clipped controller, even with zero disturbance. -/
theorem position_only_escapes : 2 < segment (1/5) unsafeInitial 0 0 := by
  have he := (ActuatorLag.exp_enclosure (h := 1/5) (by norm_num) (by norm_num)).1
  norm_num [SaturatedLag.segment, heldSegment, heldPosition, input, unsafeInitial, RobustPD.saturate] at *
  linarith

/-- This counterexample violates the actual energy-region precondition. -/
theorem outside_certified_region : 12 < TravelSafety.V unsafeInitial := by
  norm_num [TravelSafety.V, TravelSafety.P, BernsteinCertificate.energy,
    Generated.TravelQuarterLower.P, unsafeInitial, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
/-! This ablation compares sufficient Young budgets; failure of the coarse
budget is not evidence of a physically unsafe trajectory. -/
theorem coarse_response_budget_fails :
    (12 : ℝ) * (5/451) < (9471/200) * (1/5 + 1/(5/451)) * (1/100)^2 := by
  norm_num

theorem refined_response_budget_passes :
    (13 : ℝ) * (1/5 + 1/(5/451)) * (1/100)^2 < 12 * (5/451) := by
  norm_num

end LeanControls.TravelScope
