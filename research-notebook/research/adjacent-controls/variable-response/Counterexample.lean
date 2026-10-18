module
public import ComparisonEnvelope
public import StoppingCertificate
@[expose] public section
noncomputable section
namespace LeanControls.StoppingCounterexample
open Set UncertainLag StoppingCertificate VariableResponse

/-- Same uncertainty/delay assumptions, but a velocity estimate of 0.50m/s.
The true upper velocity is 0.51m/s before the delay. -/
def fastEngagement : State := ![213/8000,103/200,1/10]

theorem constant_flow_isTrajectory {H R : ℝ} (hR : R ≠ 0) (u : ℝ) (z : State) :
    IsTrajectory H (fun _ => R) (fun _ => u) (fun t => heldSolution R t u z) := by
  refine ⟨?_, fun t _ i => UncertainLag.exact_ode hR u t z i⟩
  apply Continuous.continuousOn
  apply continuous_pi
  intro i
  exact continuous_iff_continuousAt.mpr (fun t =>
    (UncertainLag.exact_ode hR u t z i).continuousAt)

/-- An admitted weak/slow trajectory already exceeds the 15cm position limit
half a second after engagement. This is an actual flow, not a failed enclosure. -/
theorem fast_case_crosses_limit :
    3/20 < heldSolution 8 (1/2) (-6/5) fastEngagement 0 := by
  have he := Real.exp_nonneg (-4)
  norm_num [heldSolution, fastEngagement]
  linarith

/-- No zero velocity has occurred before that violating position. -/
theorem fast_case_still_forward {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    0 < heldSolution 8 t (-6/5) fastEngagement 1 := by
  have he0 := Real.exp_nonneg (-(8*t))
  have he1 : Real.exp (-(8*t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hearly : t ≤ 1/5
  · norm_num [heldSolution, fastEngagement]
    nlinarith
  · have he : Real.exp (-(8*t)) ≤ 21/100 :=
      (Real.exp_le_exp.mpr (show -(8*t) ≤ -(8/5:ℝ) by linarith)).trans
        exp_neg_eight_fifths_le
    norm_num [heldSolution, fastEngagement]
    linarith

end LeanControls.StoppingCounterexample
#print axioms LeanControls.StoppingCounterexample.constant_flow_isTrajectory
#print axioms LeanControls.StoppingCounterexample.fast_case_crosses_limit
#print axioms LeanControls.StoppingCounterexample.fast_case_still_forward
