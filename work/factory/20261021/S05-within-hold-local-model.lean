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
  intro q v a δ T r hr hq t ht
  have h_abs : |r t| ≤ δ / 2 * t ^ 2 := hr t ht
  have h_bounds := (abs_le).mp h_abs
  rcases h_bounds with ⟨h_neg, h_pos⟩
  have h_nonneg : 0 ≤ δ / 2 * t ^ 2 + r t := by
    have : - (δ / 2 * t ^ 2) ≤ r t := h_neg
    linarith
  have h_quad_nonneg : 0 ≤ q + v * t + (a - δ) / 2 * t ^ 2 := hq t ht
  have h_eq : q + v * t + a / 2 * t ^ 2 + r t =
      (q + v * t + (a - δ) / 2 * t ^ 2) + (δ / 2 * t ^ 2 + r t) := by
    ring
  have : 0 ≤ q + v * t + a / 2 * t ^ 2 + r t := by
    simpa [h_eq] using add_nonneg h_quad_nonneg h_nonneg
  exact this
example : statement := solution
#print axioms solution
end Factory
