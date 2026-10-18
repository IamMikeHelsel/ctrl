import SOS

namespace SameObjectComparison

noncomputable def residual (c h x v : ℝ) : ℝ :=
  (-5 * h ^ 3 - 4 * h ^ 2 + 6 * h + 4 - c) * x ^ 2 +
  2 * (-(15 / 2) * h ^ 3 - h ^ 2 + (9 / 2) * h) * x * v +
  (-(45 / 4) * h ^ 3 + 6 * h ^ 2 - 5 * h + 4 - c) * v ^ 2

theorem baseline_residual (h x v : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ 1 / 2) :
    0 ≤ residual 1 h x v := by
  unfold residual
  sos? (config := { maxDepth := 2 })

#print axioms SameObjectComparison.baseline_residual

end SameObjectComparison
