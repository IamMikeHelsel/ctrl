import Mathlib.Tactic

/-! Conditional timing-error propagation. AI-assisted. This is elementary error
algebra, not a closed-loop safety theorem or a novelty claim. The trajectory
remainder bound is an explicit physical-model obligation. -/
namespace Research.TimingContracts

theorem timed_prediction_error
    (q₁ q₀ qhat v₀ vhat h hc H ep ev et A : ℝ)
    (h0 : 0 ≤ h) (hH : h ≤ H) (hev : 0 ≤ ev) (hA : 0 ≤ A)
    (hpos : |q₀ - qhat| ≤ ep) (hvel : |v₀ - vhat| ≤ ev)
    (htime : |h - hc| ≤ et)
    (hmodel : |q₁ - (q₀ + v₀ * h)| ≤ A / 2 * h ^ 2) :
    |q₁ - (qhat + vhat * hc)| ≤ ep + ev * H + |vhat| * et + A / 2 * H ^ 2 := by
  have hsplit : q₁ - (qhat + vhat * hc) =
      (q₁ - (q₀ + v₀ * h)) + (q₀ - qhat) + (v₀ - vhat) * h + vhat * (h - hc) := by ring
  have hsq : h ^ 2 ≤ H ^ 2 := by nlinarith
  have hr := hmodel.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hv : |(v₀ - vhat) * h| ≤ ev * H := by
    rw [abs_mul, abs_of_nonneg h0]
    exact (mul_le_mul_of_nonneg_right hvel h0).trans (mul_le_mul_of_nonneg_left hH hev)
  have ht : |vhat * (h - hc)| ≤ |vhat| * et := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left htime (abs_nonneg _)
  rw [hsplit]
  have h1 := abs_add_le (q₁ - (q₀ + v₀ * h)) (q₀ - qhat)
  have h2 := abs_add_le ((q₁ - (q₀ + v₀ * h)) + (q₀ - qhat)) ((v₀ - vhat) * h)
  have h3 := abs_add_le ((q₁ - (q₀ + v₀ * h)) + (q₀ - qhat) + (v₀ - vhat) * h) (vhat * (h - hc))
  linarith

#print axioms timed_prediction_error
end Research.TimingContracts
