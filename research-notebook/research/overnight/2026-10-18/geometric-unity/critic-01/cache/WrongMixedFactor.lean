import HyperbolicSpinor
open HyperbolicSpinor
example (f : Module.Dual ℝ ℝ) (v : ℝ) (x : ExteriorAlgebra ℝ ℝ) :
    CliffordAlgebra.contractLeft f (ExteriorAlgebra.ι ℝ v * x) +
    ExteriorAlgebra.ι ℝ v * CliffordAlgebra.contractLeft f x = (2 * f v) • x := by
  exact mixed_relation ℝ ℝ f v x
