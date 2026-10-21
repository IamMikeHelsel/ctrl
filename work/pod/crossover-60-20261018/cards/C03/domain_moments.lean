import Mathlib.Tactic
namespace C03Domain

/-- Pointwise lower jerk envelopes bound negatively weighted moment terms. -/
theorem weighted_lower (p j L : ℝ) (hp : p ≤ 0) (hj : L ≤ j) : p*j ≤ p*L := by
  exact mul_le_mul_of_nonpos_left hj hp

theorem weighted_upper (p j U : ℝ) (hp : 0 ≤ p) (hj : j ≤ U) : p*j ≤ p*U := by
  exact mul_le_mul_of_nonneg_left hj hp

/-- The three integral facts are explicit premises, not an unproved ODE inference. -/
theorem moment_gate (I0 I1 a v alpha D : ℝ)
    (ha : I0 = -a) (hv : I1 = v) (hdual : I1-alpha*I0 ≤ D) :
    v ≤ D-alpha*a := by
  rw [ha, hv] at hdual
  nlinarith

/-- Terminal j=0 contributes an extra J²/(2S) to the lower-area budget. -/
theorem source_a_j_time (T : ℝ)
    (hlower : -(51/20 : ℝ) ≥ -10*T+5/8) : 127/400 ≤ T := by linarith

theorem optimized_bound (T : ℝ) :
  let alpha : ℝ := (T+117/400)/2;
  -alpha*(51/20)+10*(alpha^2-T*alpha+T^2/2)-
    (3*alpha+T)/8+3/320 = (5/2)*T^2-(127/80)*T-13089/64000 := by
  dsimp
  ring

/-- Conditional rejection through execution-relative deadline7/8. -/
theorem reject_through_seven_eighths (T : ℝ) (hlo : 127/400 ≤ T)
    (hhi : T ≤ 7/8)
    (hgate : (2601/8000 : ℝ) ≤ (5/2)*T^2-(127/80)*T-13089/64000) : False := by
  have hprod : 0 ≤ (7/8-T)*(7/8+T-127/200) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem exact_rejection_margin :
    (2601/8000 : ℚ) - 20511/64000 = 297/64000 := by norm_num

theorem original_deadline_passes_this_gate :
    (2601/8000 : ℚ) < 108423/64000 := by norm_num

#print axioms weighted_lower
#print axioms weighted_upper
#print axioms moment_gate
#print axioms source_a_j_time
#print axioms optimized_bound
#print axioms reject_through_seven_eighths
#print axioms exact_rejection_margin
#print axioms original_deadline_passes_this_gate
end C03Domain
