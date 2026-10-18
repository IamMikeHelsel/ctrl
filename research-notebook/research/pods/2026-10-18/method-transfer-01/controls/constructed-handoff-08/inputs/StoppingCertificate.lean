module
public import LeanControls.UncertainLag
@[expose] public section
noncomputable section
namespace LeanControls.StoppingCertificate
open LeanControls.UncertainLag

/-- Upper state at brake engagement for x_hat=0 ±1mm,
v_hat=0.40 ±0.01m/s, delay<=50ms and pending acceleration<=0.1m/s^2. -/
def engagementUpper : State := ![173/8000, 83/200, 1/10]

theorem exp_neg_eight_fifths_le : Real.exp (-(8/5:ℝ)) ≤ 21/100 := by
  have hp := Real.sum_le_exp_of_nonneg (show 0 ≤ (8/5:ℝ) by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-(8/5:ℝ)))
  have he : Real.exp (-(8/5:ℝ)) * Real.exp (8/5:ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he] at hm
  linarith

/-- A concrete full-time upper-flow certificate. It covers every real t>=0,
including the peak before velocity becomes negative. -/
theorem upper_position_le {t : ℝ} (ht : 0 ≤ t) :
    heldSolution 8 t (-6/5) engagementUpper 0 ≤ 3/20 := by
  have he0 := Real.exp_nonneg (-8*t)
  have he1 : Real.exp (-(8*t)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  by_cases hearly : t ≤ 1/5
  · norm_num [heldSolution, engagementUpper]
    nlinarith [sq_nonneg t]
  · have he : Real.exp (-(8*t)) ≤ 21/100 :=
      (Real.exp_le_exp.mpr (show -(8*t) ≤ -(8/5:ℝ) by linarith)).trans
        exp_neg_eight_fifths_le
    norm_num [heldSolution, engagementUpper]
    nlinarith [sq_nonneg (t-(77/160:ℝ))]

/-- The worst admitted upper velocity is negative by half a second after
engagement. Total time from a stop request is at most 0.55s. -/
theorem upper_velocity_by_half_second :
    heldSolution 8 (1/2) (-6/5) engagementUpper 1 ≤ 0 := by
  have he := Real.exp_nonneg (-4)
  norm_num [heldSolution, engagementUpper]
  linarith

/-- The physical-unit upper state follows from the stated delay bounds.
This is the arithmetic part; a separate delay trajectory proof supplies the
polynomial position/velocity bounds. -/
theorem delay_state_arithmetic {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 1/20) :
    (1/1000:ℝ)+(41/100)*D+(1/10)*D^2/2 ≤ engagementUpper 0 ∧
    (41/100:ℝ)+(1/10)*D ≤ engagementUpper 1 := by
  norm_num [engagementUpper]
  constructor <;> nlinarith [sq_nonneg (D-1/20)]

end LeanControls.StoppingCertificate
#print axioms LeanControls.StoppingCertificate.exp_neg_eight_fifths_le
#print axioms LeanControls.StoppingCertificate.upper_position_le
#print axioms LeanControls.StoppingCertificate.upper_velocity_by_half_second
#print axioms LeanControls.StoppingCertificate.delay_state_arithmetic
