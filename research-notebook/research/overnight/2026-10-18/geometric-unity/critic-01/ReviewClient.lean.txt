import SplitSpinor

noncomputable section
open HyperbolicSpinor GUClifford

example : Module.finrank ℝ S7 = 128 := spinor_finrank
example : Module.finrank ℝ Cl = 16384 := clifford_finrank
example (a b : Cl) : splitMatrix (a * b) = splitMatrix a * splitMatrix b :=
  splitMatrix_mul a b

example (v : V) : QuadraticForm.dualProd ℝ W7 (splitLinear v) = Q v :=
  splitLinear_form v

example : splitMatrix (gamma 0) * splitMatrix (gamma 0) = 1 := positive_square
example : splitMatrix (gamma 7) * splitMatrix (gamma 7) = -1 := negative_square
example : splitMatrix (gamma 0) ≠ 0 := positive_not_zero

-- The mixed relation is witnessed on the actual exterior unit, not an assumed law.
def unitFunctional : Module.Dual ℝ ℝ := LinearMap.id
example :
    CliffordAlgebra.contractLeft unitFunctional
      (ExteriorAlgebra.ι ℝ (1 : ℝ) * (1 : ExteriorAlgebra ℝ ℝ)) +
    ExteriorAlgebra.ι ℝ (1 : ℝ) *
      CliffordAlgebra.contractLeft unitFunctional (1 : ExteriorAlgebra ℝ ℝ) = 1 := by
  simp [unitFunctional]

example :
    CliffordAlgebra.contractLeft unitFunctional
      (ExteriorAlgebra.ι ℝ (1 : ℝ) * (1 : ExteriorAlgebra ℝ ℝ)) +
    ExteriorAlgebra.ι ℝ (1 : ℝ) *
      CliffordAlgebra.contractLeft unitFunctional (1 : ExteriorAlgebra ℝ ℝ) ≠ 2 := by
  simp only [unitFunctional, mul_one, CliffordAlgebra.contractLeft_ι,
    CliffordAlgebra.contractLeft_one, mul_zero, add_zero, LinearMap.id_apply]
  intro h
  have hh : (1 : ExteriorAlgebra ℝ ℝ) + 0 = 1 + 1 := by
    simpa only [map_one, add_zero, one_add_one_eq_two] using h
  exact zero_ne_one (add_left_cancel hh)

-- Every scalar unit reaches its matching scalar matrix. The representation is unital.
example : splitMatrix 1 ≠ 0 := by
  rw [splitMatrix_one]
  exact one_ne_zero

-- Equal dimensions alone cannot certify an arbitrary linear map.
example : ¬ Function.Injective (0 : ℝ →ₗ[ℝ] ℝ) := by
  intro h
  have he : (0 : ℝ) = 1 := h (by simp)
  norm_num at he
