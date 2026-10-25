import Mathlib
set_option maxHeartbeats 400000
namespace Factory
def statement : Prop :=
  ∀ (q v a δ T : ℝ) (r : ℝ → ℝ),
    (∀ t ∈ Set.Icc (0 : ℝ) T, |r t| ≤ δ / 2 * t^2) →
    (∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ q + v*t + (a-δ)/2*t^2) →
    ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ q + v*t + a/2*t^2 + r t
theorem solution : statement := by
  unfold statement
  intro q v a δ T r hrem hnom t ht
  have hr := (abs_le.mp (hrem t ht)).1
  have hn := hnom t ht
  nlinarith
example : statement := solution
#print axioms solution
end Factory
