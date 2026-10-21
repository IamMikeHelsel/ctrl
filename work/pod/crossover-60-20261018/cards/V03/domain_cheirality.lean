import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith

/- Four-pose cheirality checks for the already fixed E_A fixture.
   This does not prove completeness of essential-matrix decomposition. -/
set_option autoImplicit false
open Matrix
namespace V03Cheirality

theorem reversed_translation_rejected (u v parallax d1 d2 : ℝ)
    (hp : 0 < parallax) (hd1 : 0 < d1)
    (relation : d2 • (![u+parallax,v,1] : Fin 3 → ℝ) =
      d1 • ![u,v,1] + ![-1,0,0]) : False := by
  have hx := congrFun relation 0
  have hz := congrFun relation 2
  simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hx hz
  rw [hz] at hx
  nlinarith [mul_pos hd1 hp]

theorem half_turn_candidates_rejected (u v parallax d1 d2 tx : ℝ)
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (relation : d2 • (![u+parallax,v,1] : Fin 3 → ℝ) =
      (!![1,0,0;0,-1,0;0,0,-1] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        (d1 • ![u,v,1]) + ![tx,0,0]) : False := by
  have hz := congrFun relation 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hz
  linarith

theorem surviving_translation_depth_forced (u v parallax d1 d2 : ℝ)
    (relation : d2 • (![u+parallax,v,1] : Fin 3 → ℝ) =
      d1 • ![u,v,1] + ![1,0,0]) :
    d2 = d1 ∧ d1 * parallax = 1 := by
  have hx := congrFun relation 0
  have hz := congrFun relation 2
  simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hx hz
  rw [hz] at hx
  constructor
  · linarith
  · nlinarith

#print axioms reversed_translation_rejected
#print axioms half_turn_candidates_rejected
#print axioms surviving_translation_depth_forced
end V03Cheirality
