import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
A local algebra check for Geometric Unity, 2021 draft, §§3.1 and 3.5,
equations (3.8)-(3.9). This is established quadratic-form algebra, not a proof
of Geometric Unity. We use six positive and four negative as an unambiguous
sign count. The author's ordered pair is (4,6).

For a symmetric covariant tensor A and g = diag(1,-1,-1,-1), the unmodified
contraction is tr(g⁻¹ A g⁻¹ A). The trace part has norm tr(g⁻¹ A)^2 / 4.
Reversing its sign therefore subtracts tr(g⁻¹ A)^2 / 2.
-/

noncomputable section

namespace WeinsteinLocalCheck

abbrev Coordinates := Fin 10 → ℝ

/-- Order: four diagonal entries, then 01,02,03,12,13,23. -/
def tensor (x : Coordinates) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![x 0, x 4, x 5, x 6;
     x 4, x 1, x 7, x 8;
     x 5, x 7, x 2, x 9;
     x 6, x 8, x 9, x 3]

def metric : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,-1,-1,-1]

/-- A concrete coordinate change, including an unchanged off-diagonal block. -/
def toDiagonal (x : Coordinates) : Coordinates :=
  ![(x 0 - x 1 - x 2 - x 3)/2,
    (x 0 - x 1 + x 2 + x 3)/2,
    (x 0 + x 1 - x 2 + x 3)/2,
    (x 0 + x 1 + x 2 - x 3)/2,
    x 4, x 5, x 6, x 7, x 8, x 9]

def fromDiagonal (y : Coordinates) : Coordinates :=
  ![(y 0 + y 1 + y 2 + y 3)/2,
    (-y 0 - y 1 + y 2 + y 3)/2,
    (-y 0 + y 1 - y 2 + y 3)/2,
    (-y 0 + y 1 + y 2 - y 3)/2,
    y 4, y 5, y 6, y 7, y 8, y 9]

theorem left_inverse (x : Coordinates) : fromDiagonal (toDiagonal x) = x := by
  ext i
  fin_cases i <;> simp [fromDiagonal, toDiagonal] <;> ring

theorem right_inverse (x : Coordinates) : toDiagonal (fromDiagonal x) = x := by
  ext i
  fin_cases i <;> simp [fromDiagonal, toDiagonal] <;> ring

noncomputable def diagonalEquiv : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun := toDiagonal
  invFun := fromDiagonal
  left_inv := left_inverse
  right_inv := right_inverse
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [toDiagonal] <;> ring
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp [toDiagonal] <;> ring

def weights : Fin 10 → ℝ := ![-1,1,1,1,-2,-2,-2,2,2,2]

noncomputable def diagonalForm : QuadraticForm ℝ Coordinates :=
  QuadraticMap.weightedSumSquares ℝ weights

noncomputable def modifiedForm : QuadraticForm ℝ Coordinates :=
  diagonalForm.comp diagonalEquiv.toLinearMap

/-- Link the formal quadratic form to the matrix contraction in the paper.
This is the substantive algebraic identity, not an assumed bridge. -/
theorem modifiedForm_eq_contraction (x : Coordinates) :
    modifiedForm x = Matrix.trace (metric * tensor x * metric * tensor x) -
      (Matrix.trace (metric * tensor x)) ^ 2 / 2 := by
  simp [modifiedForm, diagonalForm, QuadraticMap.weightedSumSquares_apply,
    diagonalEquiv, toDiagonal, weights, metric, tensor,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring


/-- This metric is its own inverse, so the contraction uses g inverse as required. -/
theorem metric_inverse : metric * metric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [metric, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Remove the metric trace, leaving the nine-dimensional trace-free component. -/
def traceFreeTensor (x : Coordinates) : Matrix (Fin 4) (Fin 4) ℝ :=
  tensor x - (Matrix.trace (metric * tensor x) / 4) • metric

theorem traceFreeTensor_has_zero_trace (x : Coordinates) :
    Matrix.trace (metric * traceFreeTensor x) = 0 := by
  simp [traceFreeTensor, metric, tensor, Matrix.trace, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_succ]
  ring

/-- The modified form keeps the trace-free contraction and reverses the trace part.
This establishes that the subtraction is the intended trace-sign choice. -/
theorem modifiedForm_reverses_trace (x : Coordinates) :
    modifiedForm x =
      Matrix.trace (metric * traceFreeTensor x * metric * traceFreeTensor x) -
        (Matrix.trace (metric * tensor x)) ^ 2 / 4 := by
  rw [modifiedForm_eq_contraction]
  simp [traceFreeTensor, metric, tensor, Matrix.trace, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_succ]
  ring

theorem tensor_symmetric (x : Coordinates) : (tensor x).transpose = tensor x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensor, Matrix.transpose_apply]

theorem tensor_injective : Function.Injective tensor := by
  intro x y h
  ext i
  fin_cases i
  all_goals first
  | exact congrArg (fun m => m 0 0) h
  | exact congrArg (fun m => m 1 1) h
  | exact congrArg (fun m => m 2 2) h
  | exact congrArg (fun m => m 3 3) h
  | exact congrArg (fun m => m 0 1) h
  | exact congrArg (fun m => m 0 2) h
  | exact congrArg (fun m => m 0 3) h
  | exact congrArg (fun m => m 1 2) h
  | exact congrArg (fun m => m 1 3) h
  | exact congrArg (fun m => m 2 3) h

/-- Every symmetric 4 by 4 matrix is covered by these ten coordinates. -/
theorem tensor_surjective_onto_symmetric (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : A.transpose = A) : ∃ x, tensor x = A := by
  refine ⟨![A 0 0, A 1 1, A 2 2, A 3 3,
    A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3], ?_⟩
  ext i j
  have hs (i j : Fin 4) : A j i = A i j := congrArg (fun m => m i j) hA
  fin_cases i <;> fin_cases j <;> simp [tensor] <;> first | exact hs _ _

noncomputable def toDiagonalIsometry : modifiedForm.IsometryEquiv diagonalForm :=
  (QuadraticMap.isometryEquivOfCompLinearEquiv diagonalForm diagonalEquiv).symm

theorem positive_count : sigPos modifiedForm = 6 := by
  rw [(show modifiedForm.Equivalent diagonalForm from ⟨toDiagonalIsometry⟩).sigPos_eq]
  change sigPos (QuadraticMap.weightedSumSquares ℝ weights) = 6
  rw [QuadraticForm.sigPos_weightedSumSquares]
  have hp : {i : Fin 10 | 0 < weights i} = {1,2,3,7,8,9} := by
    ext i
    fin_cases i <;> norm_num [weights]
  rw [hp]
  norm_num

theorem negative_count : sigNeg modifiedForm = 4 := by
  rw [(show modifiedForm.Equivalent diagonalForm from ⟨toDiagonalIsometry⟩).sigNeg_eq]
  change sigNeg (QuadraticMap.weightedSumSquares ℝ weights) = 4
  rw [QuadraticForm.sigNeg_weightedSumSquares]
  have hn : {i : Fin 10 | weights i < 0} = {0,4,5,6} := by
    ext i
    fin_cases i <;> norm_num [weights]
  rw [hn]
  norm_num

end WeinsteinLocalCheck
