module
public import LeanControls.DiagonalLyapunov
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Spectrum

/-!
Orthogonal changes of basis for the real Lyapunov operator.

These are standard reduction lemmas, not a resolution of the open six-dimensional
symmetric-maximizer problem. We use the sum of squared entries throughout, avoiding
any ambiguity about the norm on matrices.
-/
@[expose] public section
noncomputable section
namespace LeanControls.OrthogonalLyapunov
open Matrix
open DiagonalLyapunov (frobeniusSquared)
variable {n : Type*} [Fintype n] [DecidableEq n]

def conjugate (Q X : Matrix n n ℝ) : Matrix n n ℝ := Q * X * Q.transpose

def lyapunov (A X : Matrix n n ℝ) : Matrix n n ℝ := A * X + X * A.transpose

/-- The precise real squared-Frobenius version of symmetric norm attainment. -/
def HasSymmetricMaximizer (A : Matrix n n ℝ) : Prop :=
  ∃ S : Matrix n n ℝ, S.transpose = S ∧ frobeniusSquared S = 1 ∧
    ∀ X : Matrix n n ℝ, frobeniusSquared X = 1 →
      frobeniusSquared (lyapunov A X) ≤ frobeniusSquared (lyapunov A S)

omit [DecidableEq n] in
theorem frobeniusSquared_eq_trace (X : Matrix n n ℝ) :
    frobeniusSquared X = Matrix.trace (X.transpose * X) := by
  simp only [frobeniusSquared, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, sq]
  exact Finset.sum_comm

omit [DecidableEq n] in
theorem conjugate_transpose (Q X : Matrix n n ℝ) :
    (conjugate Q X).transpose = conjugate Q X.transpose := by
  simp [conjugate, Matrix.transpose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem conjugate_symmetric (Q X : Matrix n n ℝ) (hX : X.transpose = X) :
    (conjugate Q X).transpose = conjugate Q X := by
  rw [conjugate_transpose, hX]

theorem conjugate_inverse (Q X : Matrix n n ℝ) (hQ : Q.transpose * Q = 1) :
    conjugate Q.transpose (conjugate Q X) = X := by
  simp only [conjugate, Matrix.transpose_transpose]
  calc
    Q.transpose * (Q * X * Q.transpose) * Q =
        (Q.transpose * Q) * X * (Q.transpose * Q) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hQ]; simp

theorem frobeniusSquared_conjugate (Q X : Matrix n n ℝ)
    (hQ : Q.transpose * Q = 1) :
    frobeniusSquared (conjugate Q X) = frobeniusSquared X := by
  rw [frobeniusSquared_eq_trace, conjugate_transpose]
  unfold conjugate
  have hmul : Q * X.transpose * Q.transpose * (Q * X * Q.transpose) =
      Q * (X.transpose * X) * Q.transpose := by
    calc
      _ = Q * X.transpose * (Q.transpose * Q) * X * Q.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hmul, Matrix.trace_mul_cycle, hQ, Matrix.one_mul,
    ← frobeniusSquared_eq_trace]

theorem lyapunov_conjugate (Q A X : Matrix n n ℝ)
    (hQ : Q.transpose * Q = 1) :
    lyapunov (conjugate Q A) (conjugate Q X) = conjugate Q (lyapunov A X) := by
  unfold lyapunov
  rw [conjugate_transpose]
  unfold conjugate
  have hmul (B C : Matrix n n ℝ) :
      Q * B * Q.transpose * (Q * C * Q.transpose) = Q * (B * C) * Q.transpose := by
    calc
      _ = Q * B * (Q.transpose * Q) * C * Q.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hmul A X, hmul X A.transpose]
  simp only [Matrix.mul_add, Matrix.add_mul]

theorem lyapunov_frobeniusSquared_conjugate (Q A X : Matrix n n ℝ)
    (hQ : Q.transpose * Q = 1) :
    frobeniusSquared (lyapunov (conjugate Q A) (conjugate Q X)) =
      frobeniusSquared (lyapunov A X) := by
  rw [lyapunov_conjugate Q A X hQ, frobeniusSquared_conjugate Q _ hQ]

theorem hasSymmetricMaximizer_conjugate (Q A : Matrix n n ℝ)
    (hQ : Q.transpose * Q = 1) (hQ' : Q * Q.transpose = 1)
    (hA : HasSymmetricMaximizer A) : HasSymmetricMaximizer (conjugate Q A) := by
  obtain ⟨S, hS, hSunit, hSmax⟩ := hA
  refine ⟨conjugate Q S, conjugate_symmetric Q S hS, ?_, ?_⟩
  · rw [frobeniusSquared_conjugate Q S hQ, hSunit]
  · intro X hX
    have hQT : Q.transpose.transpose * Q.transpose = 1 := by simpa using hQ'
    have hXunit : frobeniusSquared (conjugate Q.transpose X) = 1 := by
      rw [frobeniusSquared_conjugate Q.transpose X hQT, hX]
    have hbound := hSmax (conjugate Q.transpose X) hXunit
    have hXback : conjugate Q (conjugate Q.transpose X) = X := by
      simpa using conjugate_inverse Q.transpose X hQT
    rw [← lyapunov_frobeniusSquared_conjugate Q A _ hQ, hXback] at hbound
    rw [lyapunov_frobeniusSquared_conjugate Q A S hQ]
    exact hbound

theorem hasSymmetricMaximizer_conjugate_iff (Q A : Matrix n n ℝ)
    (hQ : Q.transpose * Q = 1) (hQ' : Q * Q.transpose = 1) :
    HasSymmetricMaximizer (conjugate Q A) ↔ HasSymmetricMaximizer A := by
  constructor
  · intro h
    have hQT : Q.transpose.transpose * Q.transpose = 1 := by simpa using hQ'
    have hQT' : Q.transpose * Q.transpose.transpose = 1 := by simpa using hQ
    have hh := hasSymmetricMaximizer_conjugate Q.transpose (conjugate Q A) hQT hQT' h
    rw [conjugate_inverse Q A hQ] at hh
    exact hh
  · exact hasSymmetricMaximizer_conjugate Q A hQ hQ'

theorem diagonal_hasSymmetricMaximizer (a : n → ℝ) (k : n)
    (hk : ∀ i, |a i| ≤ |a k|) : HasSymmetricMaximizer (Matrix.diagonal a) := by
  exact DiagonalLyapunov.symmetric_maximizer a k hk

/-- Any supplied real orthogonal diagonalization transports the elementary diagonal proof. -/
theorem orthogonally_diagonalized_hasSymmetricMaximizer
    (Q : Matrix n n ℝ) (a : n → ℝ) (k : n)
    (hQ : Q.transpose * Q = 1) (hQ' : Q * Q.transpose = 1)
    (hk : ∀ i, |a i| ≤ |a k|) :
    HasSymmetricMaximizer (conjugate Q (Matrix.diagonal a)) := by
  exact hasSymmetricMaximizer_conjugate Q _ hQ hQ'
    (diagonal_hasSymmetricMaximizer a k hk)

/-- Real symmetric coefficient matrices admit a symmetric maximizing input in every
nonzero finite dimension. This follows from the standard spectral theorem. It does
not cover the arbitrary non-symmetric matrices in the open dimension-six problem. -/
theorem symmetric_hasSymmetricMaximizer [Nonempty n] (A : Matrix n n ℝ)
    (hA : A.transpose = A) : HasSymmetricMaximizer A := by
  have hAH : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  let U := hAH.eigenvectorUnitary
  let Q : Matrix n n ℝ := U
  have hQ : Q.transpose * Q = 1 := by
    simpa only [Q, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star] using Unitary.coe_star_mul_self U
  have hQ' : Q * Q.transpose = 1 := by
    simpa only [Q, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star] using Unitary.coe_mul_star_self U
  have hdiag : A = conjugate Q (Matrix.diagonal hAH.eigenvalues) := by
    simpa [conjugate, Q, U, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hAH.spectral_theorem
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => |hAH.eigenvalues i|) Finset.univ_nonempty
  rw [hdiag]
  exact orthogonally_diagonalized_hasSymmetricMaximizer Q hAH.eigenvalues k hQ hQ'
    (fun i => hk i (Finset.mem_univ i))

end LeanControls.OrthogonalLyapunov
