module
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

/-!
Algebraic necessary conditions for a normalized coupled Lyapunov singular pair.
These identities do not assert compatibility is sufficient, do not assert generic
dimension, and do not resolve the symmetric-maximizer problem.

To avoid division, `parameter A K` is twice the symmetric parameter H in
the paper-and-pencil parametrization A = (H + Y/2) K⁻¹.
-/
@[expose] public section
noncomputable section
namespace LeanControls.CoupledLyapunov
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def parameter (A K : Matrix n n ℝ) : Matrix n n ℝ := A * K - K * A.transpose

omit [DecidableEq n] in
theorem parameter_symmetric (A K : Matrix n n ℝ) (hK : K.transpose = -K) :
    (parameter A K).transpose = parameter A K := by
  simp [parameter, Matrix.transpose_mul, hK, sub_eq_add_neg, add_comm]

omit [DecidableEq n] in
theorem parameter_reconstruction (A K Y : Matrix n n ℝ)
    (hfirst : A * K + K * A.transpose = Y) :
    parameter A K + Y = A * K + A * K := by
  rw [← hfirst]
  unfold parameter
  abel

/-- Multiplication of the coupled equations eliminates A in favor of a symmetric
parameter. Skew-symmetry is needed for the interpretation of the parameter, but
the polynomial identity itself holds for arbitrary matrices. -/
theorem coupled_elimination (A K Y : Matrix n n ℝ)
    (hfirst : A * K + K * A.transpose = Y)
    (hsecond : A.transpose * Y + Y * A = K) :
    (K * Y) * parameter A K - parameter A K * (Y * K) =
      K ^ 3 + K ^ 3 - Y ^ 2 * K - K * Y ^ 2 := by
  calc
    _ = (K * (A.transpose * Y + Y * A) * K) +
        (K * (A.transpose * Y + Y * A) * K) - Y ^ 2 * K - K * Y ^ 2 := by
      rw [← hfirst]
      unfold parameter
      noncomm_ring
    _ = _ := by rw [hsecond]; noncomm_ring

theorem coupled_commutator (A K Y : Matrix n n ℝ)
    (hfirst : A * K + K * A.transpose = Y)
    (hsecond : A.transpose * Y + Y * A = K) :
    (Y * K) * A.transpose - A.transpose * (Y * K) = Y ^ 2 - K ^ 2 := by
  calc
    _ = Y * (A * K + K * A.transpose) - (A.transpose * Y + Y * A) * K := by
      noncomm_ring
    _ = _ := by rw [hfirst, hsecond]; noncomm_ring

theorem trace_power_commutator (C B : Matrix n n ℝ) (j : ℕ) :
    Matrix.trace (C ^ j * (C * B - B * C)) = 0 := by
  rw [Matrix.mul_sub, Matrix.trace_sub]
  apply sub_eq_zero.mpr
  calc
    Matrix.trace (C ^ j * (C * B)) = Matrix.trace ((C * C ^ j) * B) := by
      rw [← Matrix.mul_assoc, ← pow_succ, pow_succ']
    _ = Matrix.trace (C ^ j * B * C) := (Matrix.trace_mul_cycle _ _ _).symm
    _ = Matrix.trace (C ^ j * (B * C)) := by rw [Matrix.mul_assoc]

/-- Every power gives a necessary trace moment. No claim of sufficiency is made. -/
theorem coupled_trace_moments (A K Y : Matrix n n ℝ)
    (hfirst : A * K + K * A.transpose = Y)
    (hsecond : A.transpose * Y + Y * A = K) (j : ℕ) :
    Matrix.trace ((Y * K) ^ j * (Y ^ 2 - K ^ 2)) = 0 := by
  rw [← coupled_commutator A K Y hfirst hsecond]
  exact trace_power_commutator (Y * K) A.transpose j

end LeanControls.CoupledLyapunov
