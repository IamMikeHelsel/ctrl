import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- AI-written isolated polynomial certificate. The displayed scalar is trace(E E^T).
This concerns an explicit compatible-matrix family, not all camera poses. -/
set_option autoImplicit false
open Matrix
namespace V03Critical

theorem branch_polynomial (a c : ℝ) :
    c^2 * (c-2*a) = 0 ↔ c = 0 ∨ c = 2*a := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · left
      nlinarith [sq_nonneg c]
    · right
      linarith
  · rintro (h | h) <;> rw [h] <;> ring

theorem cubic_entry (a c : ℝ) :
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![0,-c,0; c,0,c-a; 0,a,0]
    (((2:ℝ) • (E * Eᵀ * E) -
      (2*c^2+a^2+(c-a)^2) • E) 0 1) = c^2*(c-2*a) := by
  dsimp
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem branches_satisfy_cubic (a c : ℝ) (h : c = 0 ∨ c = 2*a) :
    let E : Matrix (Fin 3) (Fin 3) ℝ := !![0,-c,0; c,0,c-a; 0,a,0]
    (2:ℝ) • (E * Eᵀ * E) - (2*c^2+a^2+(c-a)^2) • E = 0 := by
  dsimp
  rcases h with h | h <;> rw [h] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring

#print axioms branch_polynomial
#print axioms cubic_entry
#print axioms branches_satisfy_cubic
end V03Critical
