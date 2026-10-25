import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Byers–Nash Static Duality & Common-`T` Involution Domination

This module formalizes the dimension-free algebraic foundations of the Byers–Nash
problem (`k(A) ≤ s(A)`) from `work/pod/mf13/proof/PROOF_SKETCH.md` (Theorems 1 and 2(b))
and `work/pod/mf13/NOTES.md` (Identities I1–I3):

1. **Theorem 1 (`lyap_frobInner_symm`, `lyap_frobInner_skew`)**:
   For the Lyapunov operator `L_A(X) = A X + X Aᵀ` on `n × n` real matrices:
   - If `Uᵀ = U` and `Vᵀ = V` (symmetric), then `⟨U, L_A(V)⟩_F = 2 ⟨A, U V⟩_F`.
   - If `Yᵀ = -Y` and `Kᵀ = -K` (skew-symmetric), then `⟨Y, L_A(K)⟩_F = -2 ⟨A, Y K⟩_F`.
   This reduces `k(A) ≤ s(A)` via convex duality to factoring `Y K` into convex
   combinations of products `U V` of unit symmetric matrices.

2. **Identity I1 (`lyap_mul_involution_sub`)**:
   For any matrix `K` and any matrix `T`,
   `L_A(K T) - L_A(K) T = K (T Aᵀ - Aᵀ T)`.

3. **Theorem 2(b) & Identity I3 (`common_involution_product_eq`, `common_involution_lyap_pairing`,
   `common_involution_self_pairing`)**:
   If skew-symmetric matrices `K, Y` share an anticommuting symmetric involution `T`
   (`Tᵀ = T`, `T * T = 1`, `T * K = -K * T`, `T * Y = -Y * T`), then:
   - `K * T` and `Y * T` are symmetric,
   - `‖K * T‖_F² = ‖K‖_F²` and `‖Y * T‖_F² = ‖Y‖_F²`,
   - `(Y * T) * (K * T) = -(Y * K)` (exact rank-1 symmetric product factorization),
   - `⟨Y * T, L_A(K * T)⟩_F = ⟨Y, L_A(K)⟩_F` (Identity I3),
   - In particular, when `Y = L_A(K)` shares `T` with `K`,
     `⟨L_A(K) * T, L_A(K * T)⟩_F = ‖L_A(K)‖_F²`.
-/

namespace Research.ByersNashDuality

open Matrix

variable {n : Type*} [Fintype n]

/-- The continuous-time Lyapunov operator `L_A(X) = A X + X Aᵀ`. -/
def lyap (A X : Matrix n n ℝ) : Matrix n n ℝ :=
  A * X + X * Aᵀ

/-- The Frobenius inner product `⟨X, Y⟩_F = tr(Xᵀ Y)`. -/
def frobInner (X Y : Matrix n n ℝ) : ℝ :=
  trace (Xᵀ * Y)

/-- The squared Frobenius norm `‖X‖_F² = ⟨X, X⟩_F = tr(Xᵀ X)`. -/
def frobNormSq (X : Matrix n n ℝ) : ℝ :=
  frobInner X X

/-- Symmetry of the Frobenius inner product. -/
theorem frobInner_comm (X Y : Matrix n n ℝ) :
    frobInner X Y = frobInner Y X := by
  unfold frobInner
  calc
    trace (Xᵀ * Y) = trace ((Xᵀ * Y)ᵀ) := (trace_transpose (Xᵀ * Y)).symm
    _ = trace (Yᵀ * X) := by rw [transpose_mul, transpose_transpose]

/-- Transpose invariance of the Frobenius inner product. -/
theorem frobInner_transpose (X Y : Matrix n n ℝ) :
    frobInner Xᵀ Yᵀ = frobInner X Y := by
  unfold frobInner
  rw [transpose_transpose]
  calc
    trace (X * Yᵀ) = trace (Yᵀ * X) := trace_mul_comm X Yᵀ
    _ = trace ((Yᵀ * X)ᵀ) := (trace_transpose (Yᵀ * X)).symm
    _ = trace (Xᵀ * Y) := by rw [transpose_mul, transpose_transpose]

/-- Transpose invariance of the squared Frobenius norm. -/
theorem frobNormSq_transpose (X : Matrix n n ℝ) :
    frobNormSq Xᵀ = frobNormSq X :=
  frobInner_transpose X X

/-- Negation invariance of the squared Frobenius norm. -/
theorem frobNormSq_neg (X : Matrix n n ℝ) :
    frobNormSq (-X) = frobNormSq X := by
  unfold frobNormSq frobInner
  rw [transpose_neg, neg_mul_neg]

/-- Right multiplication by a symmetric involution preserves the Frobenius inner product. -/
theorem frobInner_mul_symm_involution [DecidableEq n] (X Y T : Matrix n n ℝ)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) :
    frobInner (X * T) (Y * T) = frobInner X Y := by
  unfold frobInner
  calc
    trace ((X * T)ᵀ * (Y * T)) = trace (Tᵀ * Xᵀ * (Y * T)) := by rw [transpose_mul]
    _ = trace (T * (Xᵀ * Y * T)) := by
      rw [hT_symm, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = trace ((Xᵀ * Y * T) * T) := trace_mul_comm T (Xᵀ * Y * T)
    _ = trace (Xᵀ * Y * (T * T)) := by rw [Matrix.mul_assoc]
    _ = trace (Xᵀ * Y) := by rw [hT_inv, Matrix.mul_one]

/-- Right multiplication by a symmetric involution is a Frobenius isometry. -/
theorem frobNormSq_mul_symm_involution [DecidableEq n] (X T : Matrix n n ℝ)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) :
    frobNormSq (X * T) = frobNormSq X :=
  frobInner_mul_symm_involution X X T hT_symm hT_inv

/-- **Theorem 1a (Static Duality on `Sym_n`)**:
For symmetric matrices `U, V`, `⟨U, L_A(V)⟩_F = 2 ⟨A, U V⟩_F`. -/
theorem lyap_frobInner_symm (A U V : Matrix n n ℝ)
    (hU : Uᵀ = U) (hV : Vᵀ = V) :
    frobInner U (lyap A V) = 2 * frobInner A (U * V) := by
  unfold frobInner lyap
  rw [Matrix.mul_add, trace_add]
  have h1 : trace (Uᵀ * (A * V)) = trace (Aᵀ * (U * V)) := by
    calc
      trace (Uᵀ * (A * V)) = trace (U * (A * V)) := by rw [hU]
      _ = trace ((U * A) * V) := by rw [Matrix.mul_assoc]
      _ = trace (V * (U * A)) := trace_mul_comm (U * A) V
      _ = trace ((V * (U * A))ᵀ) := (trace_transpose (V * (U * A))).symm
      _ = trace (Aᵀ * (U * V)) := by
        rw [transpose_mul, transpose_mul, hU, hV, Matrix.mul_assoc]
  have h2 : trace (Uᵀ * (V * Aᵀ)) = trace (Aᵀ * (U * V)) := by
    calc
      trace (Uᵀ * (V * Aᵀ)) = trace ((U * V) * Aᵀ) := by
        rw [hU, Matrix.mul_assoc]
      _ = trace (Aᵀ * (U * V)) := trace_mul_comm (U * V) Aᵀ
  linarith [h1, h2]

/-- **Theorem 1b (Static Duality on `Skew_n`)**:
For skew-symmetric matrices `Y, K`, `⟨Y, L_A(K)⟩_F = -2 ⟨A, Y K⟩_F`. -/
theorem lyap_frobInner_skew (A Y K : Matrix n n ℝ)
    (hY : Yᵀ = -Y) (hK : Kᵀ = -K) :
    frobInner Y (lyap A K) = -2 * frobInner A (Y * K) := by
  unfold frobInner lyap
  rw [Matrix.mul_add, trace_add]
  have h1 : trace (Yᵀ * (A * K)) = -trace (Aᵀ * (Y * K)) := by
    calc
      trace (Yᵀ * (A * K)) = trace ((-Y) * (A * K)) := by rw [hY]
      _ = -trace ((Y * A) * K) := by rw [Matrix.neg_mul, trace_neg, Matrix.mul_assoc]
      _ = -trace (K * (Y * A)) := by rw [trace_mul_comm (Y * A) K]
      _ = -trace ((K * (Y * A))ᵀ) := by rw [← trace_transpose (K * (Y * A))]
      _ = -trace (Aᵀ * (Y * K)) := by
        have htr : (K * (Y * A))ᵀ = Aᵀ * (Y * K) := by
          rw [transpose_mul, transpose_mul, hY, hK]
          noncomm_ring
        rw [htr]
  have h2 : trace (Yᵀ * (K * Aᵀ)) = -trace (Aᵀ * (Y * K)) := by
    calc
      trace (Yᵀ * (K * Aᵀ)) = trace ((-Y) * (K * Aᵀ)) := by rw [hY]
      _ = -trace ((Y * K) * Aᵀ) := by rw [Matrix.neg_mul, trace_neg, Matrix.mul_assoc]
      _ = -trace (Aᵀ * (Y * K)) := by rw [trace_mul_comm (Y * K) Aᵀ]
  linarith [h1, h2]

/-- **Identity I1 (Lyapunov commutator with right multiplication)**:
`L_A(K T) - L_A(K) T = K (T Aᵀ - Aᵀ T)`. -/
theorem lyap_mul_involution_sub (A K T : Matrix n n ℝ) :
    lyap A (K * T) - lyap A K * T = K * (T * Aᵀ - Aᵀ * T) := by
  unfold lyap
  noncomm_ring

/-- If `K` is skew-symmetric and `T` is symmetric and anticommutes with `K`,
then `K * T` is symmetric. -/
theorem symm_of_skew_mul_anticomm (K T : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hT : Tᵀ = T) (hTK : T * K = -K * T) :
    (K * T)ᵀ = K * T := by
  calc
    (K * T)ᵀ = Tᵀ * Kᵀ := transpose_mul K T
    _ = T * (-K) := by rw [hT, hK]
    _ = -(T * K) := Matrix.mul_neg T K
    _ = -(-K * T) := by rw [hTK]
    _ = K * T := by noncomm_ring

/-- **Theorem 2(b), Part 1 (Static Product Factorization under Common `T`)**:
If `T * T = 1` and `T` anticommutes with `K`, then `(Y * T) * (K * T) = -(Y * K)`. -/
theorem common_involution_product_eq [DecidableEq n] (Y K T : Matrix n n ℝ)
    (hT_inv : T * T = 1) (hTK : T * K = -K * T) :
    (Y * T) * (K * T) = -(Y * K) := by
  have hTKT : T * (K * T) = -K := by
    calc
      T * (K * T) = (T * K) * T := (Matrix.mul_assoc T K T).symm
      _ = (-K * T) * T := by rw [hTK]
      _ = -K * (T * T) := Matrix.mul_assoc (-K) T T
      _ = -K := by rw [hT_inv, Matrix.mul_one]
  calc
    (Y * T) * (K * T) = Y * (T * (K * T)) := Matrix.mul_assoc Y T (K * T)
    _ = Y * (-K) := by rw [hTKT]
    _ = -(Y * K) := Matrix.mul_neg Y K

/-- **Theorem 2(b), Part 2 & Identity I3 (Common-`T` Lyapunov Pairing Identity)**:
If skew-symmetric `K, Y` share an anticommuting symmetric involution `T`, then the
symmetric witnesses `U = Y * T` and `V = K * T` satisfy
`⟨Y * T, L_A(K * T)⟩_F = ⟨Y, L_A(K)⟩_F`. -/
theorem common_involution_lyap_pairing [DecidableEq n] (A Y K T : Matrix n n ℝ)
    (hY : Yᵀ = -Y) (hK : Kᵀ = -K)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1)
    (hTY : T * Y = -Y * T) (hTK : T * K = -K * T) :
    frobInner (Y * T) (lyap A (K * T)) = frobInner Y (lyap A K) := by
  have hU_symm : (Y * T)ᵀ = Y * T := symm_of_skew_mul_anticomm Y T hY hT_symm hTY
  have hV_symm : (K * T)ᵀ = K * T := symm_of_skew_mul_anticomm K T hK hT_symm hTK
  have h_prod : (Y * T) * (K * T) = -(Y * K) := common_involution_product_eq Y K T hT_inv hTK
  rw [lyap_frobInner_symm A (Y * T) (K * T) hU_symm hV_symm,
    lyap_frobInner_skew A Y K hY hK, h_prod]
  unfold frobInner
  rw [Matrix.mul_neg, trace_neg]
  ring

/-- **Theorem 2(b), Part 3 (Self-Pairing Equality at `Y = L_A(K)`)**:
When `K` is skew-symmetric and `T` is a symmetric involution anticommuting with both
`K` and `L_A(K)`, the symmetric matrix `S = K * T` has `‖S‖_F² = ‖K‖_F²` and satisfies
`⟨L_A(K) * T, L_A(K * T)⟩_F = ‖L_A(K)‖_F²`. -/
theorem common_involution_self_pairing [DecidableEq n] (A K T : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hT_symm : Tᵀ = T) (hT_inv : T * T = 1)
    (hTK : T * K = -K * T) (hTL : T * lyap A K = -lyap A K * T) :
    (K * T)ᵀ = K * T ∧
      frobNormSq (K * T) = frobNormSq K ∧
      frobNormSq (lyap A K * T) = frobNormSq (lyap A K) ∧
      frobInner (lyap A K * T) (lyap A (K * T)) = frobNormSq (lyap A K) := by
  have hL_skew : (lyap A K)ᵀ = -lyap A K := by
    unfold lyap
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, hK]
    noncomm_ring
  exact ⟨symm_of_skew_mul_anticomm K T hK hT_symm hTK,
    frobNormSq_mul_symm_involution K T hT_symm hT_inv,
    frobNormSq_mul_symm_involution (lyap A K) T hT_symm hT_inv,
    common_involution_lyap_pairing A (lyap A K) K T hL_skew hK hT_symm hT_inv hTL hTK⟩

#print axioms lyap_frobInner_symm
#print axioms lyap_frobInner_skew
#print axioms lyap_mul_involution_sub
#print axioms common_involution_product_eq
#print axioms common_involution_lyap_pairing
#print axioms common_involution_self_pairing

end Research.ByersNashDuality
