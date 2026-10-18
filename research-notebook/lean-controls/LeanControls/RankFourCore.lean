module
public import LeanControls.OrthogonalLyapunov
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A conditional two-block comparison in dimension six

This proves the algebraic comparison after the relevant off-diagonal 2×2 block
has been made diagonal. It does NOT prove existence of skew canonical form or
of the required signed SVD, and is not the general rank-four exclusion theorem.
The last two coordinates have arbitrary couplings in the coefficient matrix A.
-/
@[expose] public section
noncomputable section
namespace LeanControls.RankFourCore
open Matrix
open DiagonalLyapunov (frobeniusSquared)
open OrthogonalLyapunov (lyapunov conjugate)

abbrev Mat := Matrix (Fin 6) (Fin 6) ℝ

def skewWitness (a b : ℝ) : Mat :=
  !![0, a, 0, 0, 0, 0;
    -a, 0, 0, 0, 0, 0;
     0, 0, 0, b, 0, 0;
     0, 0, -b, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

def symmetricWitness (a b : ℝ) : Mat :=
  !![0, a, 0, 0, 0, 0;
     a, 0, 0, 0, 0, 0;
     0, 0, 0, b, 0, 0;
     0, 0, b, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

theorem skewWitness_skew (a b : ℝ) : (skewWitness a b).transpose = -skewWitness a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewWitness, Matrix.transpose_apply]

theorem symmetricWitness_symmetric (a b : ℝ) :
    (symmetricWitness a b).transpose = symmetricWitness a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricWitness, Matrix.transpose_apply]

theorem same_square (a b : ℝ) :
    symmetricWitness a b * symmetricWitness a b = -(skewWitness a b * skewWitness a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricWitness, skewWitness, Matrix.mul_apply, Fin.sum_univ_succ]

theorem skewWitness_squaredNorm (a b : ℝ) :
    frobeniusSquared (skewWitness a b) = 2 * (a ^ 2 + b ^ 2) := by
  simp [frobeniusSquared, skewWitness, Fin.sum_univ_succ]
  ring

theorem same_squaredNorm (a b : ℝ) :
    frobeniusSquared (symmetricWitness a b) = frobeniusSquared (skewWitness a b) := by
  simp [frobeniusSquared, symmetricWitness, skewWitness, Fin.sum_univ_succ]

/-- The two off-diagonal entries of A's upper-right 2×2 active block vanish.
All other 34 entries of A, including the remaining-coordinate couplings, are free. -/
theorem gain_difference (A : Mat) (a b : ℝ)
    (h03 : A 0 3 = 0) (h12 : A 1 2 = 0) :
    frobeniusSquared (lyapunov A (symmetricWitness a b)) -
      frobeniusSquared (lyapunov A (skewWitness a b)) =
    4 * a ^ 2 * ((A 0 1) ^ 2 + (A 1 0) ^ 2) +
      4 * b ^ 2 * ((A 2 3) ^ 2 + (A 3 2) ^ 2) := by
  simp [frobeniusSquared, lyapunov, symmetricWitness, skewWitness,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_succ, h03, h12]
  ring

theorem gain_comparison (A : Mat) (a b : ℝ)
    (h03 : A 0 3 = 0) (h12 : A 1 2 = 0) :
    frobeniusSquared (lyapunov A (skewWitness a b)) ≤
      frobeniusSquared (lyapunov A (symmetricWitness a b)) := by
  have h := gain_difference A a b h03 h12
  have hnonneg : 0 ≤ 4 * a ^ 2 * ((A 0 1) ^ 2 + (A 1 0) ^ 2) +
      4 * b ^ 2 * ((A 2 3) ^ 2 + (A 3 2) ^ 2) := by positivity
  linarith

/-- The conditional comparison transports through any supplied orthogonal basis.
This theorem assumes the prepared block coordinates; it does not construct them. -/
theorem conjugated_comparison (Q A : Mat) (a b : ℝ)
    (hQ : Q.transpose * Q = 1)
    (h03 : A 0 3 = 0) (h12 : A 1 2 = 0) :
    ∃ S : Mat, S.transpose = S ∧
      frobeniusSquared S = frobeniusSquared (conjugate Q (skewWitness a b)) ∧
      frobeniusSquared (lyapunov (conjugate Q A) (conjugate Q (skewWitness a b))) ≤
        frobeniusSquared (lyapunov (conjugate Q A) S) := by
  refine ⟨conjugate Q (symmetricWitness a b),
    OrthogonalLyapunov.conjugate_symmetric Q _ (symmetricWitness_symmetric a b), ?_, ?_⟩
  · rw [OrthogonalLyapunov.frobeniusSquared_conjugate Q _ hQ,
      OrthogonalLyapunov.frobeniusSquared_conjugate Q _ hQ, same_squaredNorm]
  · rw [OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate Q A _ hQ,
      OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate Q A _ hQ]
    exact gain_comparison A a b h03 h12

end LeanControls.RankFourCore
