import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Research.ByersNashDuality
import Research.SkewNormalForm

/-!
# Byers–Nash $n=6$: Multi-Term Symmetric Test Family Duality & Klein 4-Group Character Decomposition

This module builds on `Research.ByersNashDuality` and `Research.SkewNormalForm` to formalize
the algebraic and harmonic-analytic machinery for the **Full-Rank Non-Common-$T$ Case**
($\operatorname{rank} K = 6$, three Darboux frequencies $a, b, c$) of the Byers–Nash problem in
dimension $n = 6$:

1. **General Involution Projections & Exact Identity (I2) (`lyap_anticomm_pairing`,
   `lyap_normSq_decomp_involution`, `lyap_gain_diff_involution`)**:
   For any symmetric involution $T$ ($T^\top = T, T^2 = 1$) anticommuting with skew-symmetric $K$
   ($T K = -K T$), decompose any matrix $X$ into its $T$-commuting part
   $X_c(T) = \frac{1}{2}(X + T X T)$ and $T$-anticommuting part $X_a(T) = \frac{1}{2}(X - T X T)$.
   - For skew-symmetric $Y$, $Y_a(T) T$ is symmetric and satisfies the exact partial pairing identity
     $$\langle Y_a(T) T, \mathcal{L}_A(K T) \rangle_F = \langle Y_a(T), \mathcal{L}_A(K) \rangle_F.$$
   - Setting $H = \frac{1}{2}(A K - K A^\top) \in \operatorname{Sym}_n$ and $Y = \mathcal{L}_A(K) \in \operatorname{Skew}_n$,
     we prove the exact orthogonal decomposition:
     $$\mathcal{L}_A(K T) = (2 H_c(T) + Y_a(T)) T,$$
     which yields Identity (I2):
     $$\|\mathcal{L}_A(K T)\|_F^2 = 4 \|H_c(T)\|_F^2 + \|Y_a(T)\|_F^2,$$
     $$\|\mathcal{L}_A(K T)\|_F^2 - \|\mathcal{L}_A(K)\|_F^2 = 4 \|H_c(T)\|_F^2 - \|Y_c(T)\|_F^2.$$

2. **Multi-Term Symmetric Test Family Duality (`byers_nash_two_term_bound`,
   `byers_nash_three_term_bound`, `byers_nash_orthogonal_involutions`)**:
   When a skew-symmetric witness $Y$ decomposes into a sum $Y = \sum_r Y_r$ of skew-symmetric
   components where each $Y_r$ anticommutes with a symmetric involution $T_r$ that anticommutes
   with $K$, the symmetric test pairs $(U_r, V_r) = (Y_r T_r, K T_r)$ satisfy:
   - $\sum_r U_r V_r = -Y K$ (exact multi-term symmetric factorization),
   - $\sum_r \langle U_r, \mathcal{L}_A(K T_r) \rangle_F = \langle Y, \mathcal{L}_A(K) \rangle_F$.

3. **Full-Rank $6 \times 6$ Darboux Normal Form & Klein 4-Group Character Theorem
   (`four_involution_parseval_decomposition`)**:
   For $K = \operatorname{diag}(a J, b J, c J)$ (`skewWitness6 a b c`), the four commuting
   symmetric orthogonal involutions
   $$T_0 = \operatorname{diag}(F, F, F), \quad T_1 = \operatorname{diag}(F, -F, -F), \quad
     T_2 = \operatorname{diag}(-F, F, -F), \quad T_3 = \operatorname{diag}(-F, -F, F)$$
   all anticommute with $K$, producing four isometric same-square symmetric comparators
   $S_r = K T_r$ ($S_r^\top = S_r$, $S_r^2 = -K^2$, $\|S_r\|_F^2 = \|K\|_F^2$).
   Their conjugation action on $\mathbb{R}^{6 \times 6}$ forms a Klein 4-group character table
   across the three $2 \times 2$ Darboux planes, isolating the block-diagonal part `diagBlocks Y`
   and each off-diagonal plane pair `blockPair12 Y`, `blockPair13 Y`, `blockPair23 Y`, and yielding
   the exact discrete Parseval identity:
   $$\sum_{r=0}^3 \|\mathcal{L}_A(K T_r)\|_F^2
     = 4 \sum_{r=0}^3 \|H_c(T_r)\|_F^2 + 2 \|\mathcal{L}_A(K)\|_F^2 + 2 \|\operatorname{diagBlocks}(\mathcal{L}_A(K))\|_F^2.$$
-/

namespace Research.ByersNashMultiTerm

open Matrix
open Research.ByersNashDuality

variable {n : Type*} [Fintype n]

/-! ## Section 1: Dimension-Free Involution Projections & Identity (I2) -/

/-- The symmetric part of `A * K` when `K` is skew-symmetric:
`H = (1/2) (A K + (A K)ᵀ) = (1/2) (A K - K Aᵀ)`. -/
noncomputable def symPart (A K : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A * K - K * Aᵀ)

/-- The `T`-commuting projection of `X`: `X_c(T) = (1/2) (X + T X T)`. -/
noncomputable def commPart (T X : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (X + T * X * T)

/-- The `T`-anticommuting projection of `X`: `X_a(T) = (1/2) (X - T X T)`. -/
noncomputable def anticommPart (T X : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (X - T * X * T)

/-- Any matrix decomposes as the sum of its `T`-anticommuting and `T`-commuting parts. -/
theorem anticommPart_add_commPart (T X : Matrix n n ℝ) :
    anticommPart T X + commPart T X = X := by
  unfold anticommPart commPart
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- If `K` is skew-symmetric, `symPart A K` is symmetric. -/
theorem symPart_transpose (A K : Matrix n n ℝ) (hK : Kᵀ = -K) :
    (symPart A K)ᵀ = symPart A K := by
  unfold symPart
  rw [transpose_smul, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hK,
    Matrix.mul_neg, Matrix.neg_mul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- If `K` is skew-symmetric, `lyap A K` is skew-symmetric. -/
theorem lyap_skew_of_skew (A K : Matrix n n ℝ) (hK : Kᵀ = -K) :
    (lyap A K)ᵀ = -lyap A K := by
  unfold lyap
  rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, hK]
  noncomm_ring

/-- If `X` is symmetric and `T` is symmetric, `commPart T X` is symmetric. -/
theorem commPart_symm (T X : Matrix n n ℝ) (hT : Tᵀ = T) (hX : Xᵀ = X) :
    (commPart T X)ᵀ = commPart T X := by
  unfold commPart
  rw [transpose_smul, transpose_add, transpose_mul, transpose_mul, hT, hX, Matrix.mul_assoc]

/-- If `Y` is skew-symmetric and `T` is symmetric, `commPart T Y` is skew-symmetric. -/
theorem commPart_skew (T Y : Matrix n n ℝ) (hT : Tᵀ = T) (hY : Yᵀ = -Y) :
    (commPart T Y)ᵀ = -commPart T Y := by
  unfold commPart
  rw [transpose_smul, transpose_add, transpose_mul, transpose_mul, hT, hY,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- If `Y` is skew-symmetric and `T` is symmetric, `anticommPart T Y` is skew-symmetric. -/
theorem anticommPart_skew (T Y : Matrix n n ℝ) (hT : Tᵀ = T) (hY : Yᵀ = -Y) :
    (anticommPart T Y)ᵀ = -anticommPart T Y := by
  unfold anticommPart
  rw [transpose_smul, transpose_sub, transpose_mul, transpose_mul, hT, hY,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- For an involution `T` (`T * T = 1`), `commPart T X` commutes with `T`. -/
theorem mul_commPart_involution [DecidableEq n] (T X : Matrix n n ℝ) (hT_inv : T * T = 1) :
    T * commPart T X = commPart T X * T := by
  unfold commPart
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  have h1 : T * (T * X * T) = X * T := by
    calc
      T * (T * X * T) = (T * T) * X * T := by simp only [Matrix.mul_assoc]
      _ = X * T := by rw [hT_inv, Matrix.one_mul]
  have h2 : (T * X * T) * T = T * X := by
    calc
      (T * X * T) * T = T * X * (T * T) := by simp only [Matrix.mul_assoc]
      _ = T * X := by rw [hT_inv, Matrix.mul_one]
  rw [h1, h2, add_comm]

/-- For an involution `T` (`T * T = 1`), `anticommPart T X` anticommutes with `T`. -/
theorem mul_anticommPart_involution [DecidableEq n] (T X : Matrix n n ℝ) (hT_inv : T * T = 1) :
    T * anticommPart T X = -anticommPart T X * T := by
  unfold anticommPart
  have h1 : T * (T * X * T) = X * T := by
    calc
      T * (T * X * T) = (T * T) * X * T := by simp only [Matrix.mul_assoc]
      _ = X * T := by rw [hT_inv, Matrix.one_mul]
  have h2 : (T * X * T) * T = T * X := by
    calc
      (T * X * T) * T = T * X * (T * T) := by simp only [Matrix.mul_assoc]
      _ = T * X := by rw [hT_inv, Matrix.mul_one]
  rw [Matrix.mul_smul, Matrix.mul_sub, h1, Matrix.neg_mul, Matrix.smul_mul, Matrix.sub_mul, h2]
  ext i j
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- Any symmetric matrix is Frobenius-orthogonal to any skew-symmetric matrix. -/
theorem frobInner_symm_skew_eq_zero (U W : Matrix n n ℝ)
    (hU : Uᵀ = U) (hW : Wᵀ = -W) :
    frobInner U W = 0 := by
  have h1 : frobInner U W = -frobInner U W := by
    calc
      frobInner U W = frobInner Uᵀ Wᵀ := (frobInner_transpose U W).symm
      _ = frobInner U (-W) := by rw [hU, hW]
      _ = -frobInner U W := by
        unfold frobInner
        rw [Matrix.mul_neg, trace_neg]
  linarith

/-- Pythagorean identity for Frobenius norm squared of orthogonal matrices. -/
theorem frobNormSq_add_of_frobInner_eq_zero (X Y : Matrix n n ℝ)
    (horth : frobInner X Y = 0) :
    frobNormSq (X + Y) = frobNormSq X + frobNormSq Y := by
  unfold frobNormSq frobInner
  have hyx : trace (Yᵀ * X) = 0 := by
    have hc := frobInner_comm X Y
    unfold frobInner at hc horth
    linarith
  rw [transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    trace_add, trace_add, trace_add]
  unfold frobInner at horth
  linarith

/-- Left and right multiplication by a symmetric involution is a Frobenius isometry. -/
theorem frobInner_conj_symm_involution [DecidableEq n] (X Y T : Matrix n n ℝ)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) :
    frobInner (T * X * T) (T * Y * T) = frobInner X Y := by
  rw [frobInner_mul_symm_involution (T * X) (T * Y) T hT_symm hT_inv]
  unfold frobInner
  calc
    trace ((T * X)ᵀ * (T * Y)) = trace (Xᵀ * Tᵀ * (T * Y)) := by rw [transpose_mul]
    _ = trace (Xᵀ * (T * T) * Y) := by
      rw [hT_symm]
      simp only [Matrix.mul_assoc]
    _ = trace (Xᵀ * Y) := by rw [hT_inv, Matrix.mul_one]

/-- Orthogonality of `anticommPart T X` and `commPart T X` for a symmetric involution `T`. -/
theorem frobInner_anticommPart_commPart [DecidableEq n] (T X : Matrix n n ℝ)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) :
    frobInner (anticommPart T X) (commPart T X) = 0 := by
  have h_norm : frobInner (T * X * T) (T * X * T) = frobInner X X :=
    frobInner_conj_symm_involution X X T hT_symm hT_inv
  have h_comm : frobInner X (T * X * T) = frobInner (T * X * T) X :=
    frobInner_comm X (T * X * T)
  unfold anticommPart commPart frobInner
  rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul,
    transpose_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add,
    trace_sub, trace_add, trace_add]
  simp only [smul_eq_mul]
  unfold frobInner at h_norm h_comm
  linarith

/-- Pythagorean decomposition `‖X‖_F² = ‖X_a(T)‖_F² + ‖X_c(T)‖_F²`. -/
theorem frobNormSq_eq_anticommPart_add_commPart [DecidableEq n] (T X : Matrix n n ℝ)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) :
    frobNormSq X = frobNormSq (anticommPart T X) + frobNormSq (commPart T X) := by
  conv_lhs => rw [← anticommPart_add_commPart T X]
  exact frobNormSq_add_of_frobInner_eq_zero (anticommPart T X) (commPart T X)
    (frobInner_anticommPart_commPart T X hT_symm hT_inv)

/-- Partial pairing identity: for any skew-symmetric `Y, K` and symmetric involution `T`
anticommuting with `K`, `(anticommPart T Y) * T` is symmetric and satisfies
`⟨anticommPart T Y * T, L_A(K * T)⟩_F = ⟨anticommPart T Y, L_A(K)⟩_F`. -/
theorem lyap_anticomm_pairing [DecidableEq n] (A Y K T : Matrix n n ℝ)
    (hY : Yᵀ = -Y) (hK : Kᵀ = -K)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) (hTK : T * K = -K * T) :
    (anticommPart T Y * T)ᵀ = anticommPart T Y * T ∧
      frobInner (anticommPart T Y * T) (lyap A (K * T)) =
        frobInner (anticommPart T Y) (lyap A K) := by
  have hYa_skew : (anticommPart T Y)ᵀ = -anticommPart T Y := anticommPart_skew T Y hT_symm hY
  have hYa_anti : T * anticommPart T Y = -anticommPart T Y * T :=
    mul_anticommPart_involution T Y hT_inv
  exact ⟨symm_of_skew_mul_anticomm (anticommPart T Y) T hYa_skew hT_symm hYa_anti,
    common_involution_lyap_pairing A (anticommPart T Y) K T hYa_skew hK hT_symm hT_inv hYa_anti hTK⟩

/-- Exact matrix decomposition of `L_A(K T)` into symmetric and skew-symmetric components:
`L_A(K T) = (2 • commPart T (symPart A K) + anticommPart T (lyap A K)) * T`. -/
theorem lyap_mul_involution_decomp [DecidableEq n] (A K T : Matrix n n ℝ)
    (hT_inv : T * T = 1) (hTK : T * K = -K * T) :
    lyap A (K * T) =
      ((2 : ℝ) • commPart T (symPart A K) + anticommPart T (lyap A K)) * T := by
  unfold lyap commPart anticommPart symPart
  have hTKT : ∀ M : Matrix n n ℝ, (T * M * T) * T = T * M := by
    intro M
    calc
      (T * M * T) * T = T * M * (T * T) := by simp only [Matrix.mul_assoc]
      _ = T * M := by rw [hT_inv, Matrix.mul_one]
  have hKT : K * T * Aᵀ = -(T * (K * Aᵀ)) := by
    have hKT' : K * T = -(T * K) := by
      rw [hTK, Matrix.neg_mul, neg_neg]
    rw [hKT', Matrix.neg_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc A K T, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.add_mul, Matrix.sub_mul, hTKT, hTKT, hKT,
    Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_sub,
    Matrix.add_mul, Matrix.mul_add]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Scalar multiplication law for `frobNormSq`. -/
theorem frobNormSq_smul (c : ℝ) (X : Matrix n n ℝ) :
    frobNormSq (c • X) = c ^ 2 * frobNormSq X := by
  unfold frobNormSq frobInner
  rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul]
  simp only [smul_eq_mul]
  ring

/-- **Identity (I2), Part 1 (`lyap_normSq_decomp_involution`)**:
For any skew-symmetric `K` and symmetric involution `T` with `T K = -K T`,
`‖L_A(K T)‖_F² = 4 ‖H_c(T)‖_F² + ‖Y_a(T)‖_F²`, where `H = symPart A K` and `Y = L_A(K)`. -/
theorem lyap_normSq_decomp_involution [DecidableEq n] (A K T : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) (hTK : T * K = -K * T) :
    frobNormSq (lyap A (K * T)) =
      4 * frobNormSq (commPart T (symPart A K)) +
        frobNormSq (anticommPart T (lyap A K)) := by
  rw [lyap_mul_involution_decomp A K T hT_inv hTK,
    frobNormSq_mul_symm_involution _ T hT_symm hT_inv]
  have hH_symm : ((2 : ℝ) • commPart T (symPart A K))ᵀ = (2 : ℝ) • commPart T (symPart A K) := by
    rw [transpose_smul, commPart_symm T (symPart A K) hT_symm (symPart_transpose A K hK)]
  have hY_skew : (anticommPart T (lyap A K))ᵀ = -anticommPart T (lyap A K) :=
    anticommPart_skew T (lyap A K) hT_symm (lyap_skew_of_skew A K hK)
  rw [frobNormSq_add_of_frobInner_eq_zero _ _ (frobInner_symm_skew_eq_zero _ _ hH_symm hY_skew),
    frobNormSq_smul 2 (commPart T (symPart A K))]
  ring

/-- **Identity (I2), Part 2 (`lyap_gain_diff_involution`)**:
For any skew-symmetric `K` and symmetric involution `T` with `T K = -K T`,
`‖L_A(K T)‖_F² - ‖L_A(K)‖_F² = 4 ‖H_c(T)‖_F² - ‖Y_c(T)‖_F²`. -/
theorem lyap_gain_diff_involution [DecidableEq n] (A K T : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) (hTK : T * K = -K * T) :
    frobNormSq (lyap A (K * T)) - frobNormSq (lyap A K) =
      4 * frobNormSq (commPart T (symPart A K)) -
        frobNormSq (commPart T (lyap A K)) := by
  have h1 := lyap_normSq_decomp_involution A K T hK hT_symm hT_inv hTK
  have h2 := frobNormSq_eq_anticommPart_add_commPart T (lyap A K) hT_symm hT_inv
  linarith

/-! ## Section 2: Multi-Term Symmetric Test Family Duality -/

/-- Additivity of `frobInner` in the left argument. -/
theorem frobInner_add_left (X₁ X₂ Y : Matrix n n ℝ) :
    frobInner (X₁ + X₂) Y = frobInner X₁ Y + frobInner X₂ Y := by
  unfold frobInner
  rw [transpose_add, Matrix.add_mul, trace_add]

/-- **Two-Term Symmetric Test Family Duality (`byers_nash_two_term_bound`)**:
Suppose `T₁, T₂` are symmetric involutions anticommuting with skew-symmetric `K`,
and a skew-symmetric matrix `Y = Y₁ + Y₂` decomposes into skew-symmetric pieces `Y₁, Y₂`
such that `T₁` anticommutes with `Y₁` and `T₂` anticommutes with `Y₂`.
Then `U₁ = Y₁ T₁`, `U₂ = Y₂ T₂`, `V₁ = K T₁`, `V₂ = K T₂` are all symmetric, and:
1. `U₁ * V₁ + U₂ * V₂ = -(Y * K)` (two-term symmetric product factorization),
2. `⟨U₁, L_A(V₁)⟩_F + ⟨U₂, L_A(V₂)⟩_F = ⟨Y, L_A(K)⟩_F`. -/
theorem byers_nash_two_term_bound [DecidableEq n]
    (A Y Y₁ Y₂ K T₁ T₂ : Matrix n n ℝ)
    (hY : Y = Y₁ + Y₂)
    (hY₁ : Y₁ᵀ = -Y₁) (hY₂ : Y₂ᵀ = -Y₂) (hK : Kᵀ = -K)
    (hT₁_symm : T₁ᵀ = T₁) (hT₁_inv : T₁ * T₁ = 1)
    (hT₂_symm : T₂ᵀ = T₂) (hT₂_inv : T₂ * T₂ = 1)
    (hT₁Y₁ : T₁ * Y₁ = -Y₁ * T₁) (hT₂Y₂ : T₂ * Y₂ = -Y₂ * T₂)
    (hT₁K : T₁ * K = -K * T₁) (hT₂K : T₂ * K = -K * T₂) :
    (Y₁ * T₁)ᵀ = Y₁ * T₁ ∧
    (Y₂ * T₂)ᵀ = Y₂ * T₂ ∧
    (K * T₁)ᵀ = K * T₁ ∧
    (K * T₂)ᵀ = K * T₂ ∧
    (Y₁ * T₁) * (K * T₁) + (Y₂ * T₂) * (K * T₂) = -(Y * K) ∧
    frobInner (Y₁ * T₁) (lyap A (K * T₁)) + frobInner (Y₂ * T₂) (lyap A (K * T₂)) =
      frobInner Y (lyap A K) := by
  refine ⟨symm_of_skew_mul_anticomm Y₁ T₁ hY₁ hT₁_symm hT₁Y₁,
    symm_of_skew_mul_anticomm Y₂ T₂ hY₂ hT₂_symm hT₂Y₂,
    symm_of_skew_mul_anticomm K T₁ hK hT₁_symm hT₁K,
    symm_of_skew_mul_anticomm K T₂ hK hT₂_symm hT₂K, ?_, ?_⟩
  · rw [common_involution_product_eq Y₁ K T₁ hT₁_inv hT₁K,
      common_involution_product_eq Y₂ K T₂ hT₂_inv hT₂K, hY]
    noncomm_ring
  · rw [common_involution_lyap_pairing A Y₁ K T₁ hY₁ hK hT₁_symm hT₁_inv hT₁Y₁ hT₁K,
      common_involution_lyap_pairing A Y₂ K T₂ hY₂ hK hT₂_symm hT₂_inv hT₂Y₂ hT₂K,
      hY, frobInner_add_left]

/-- **Three-Term Symmetric Test Family Duality (`byers_nash_three_term_bound`)**:
Suppose `T₁, T₂, T₃` are symmetric involutions anticommuting with skew-symmetric `K`,
and a skew-symmetric matrix `Y = Y₁ + Y₂ + Y₃` decomposes into skew-symmetric pieces `Y₁, Y₂, Y₃`
such that `T_r` anticommutes with `Y_r` for `r = 1, 2, 3`.
Then `U_r = Y_r T_r` and `V_r = K T_r` are symmetric and satisfy:
1. `U₁ * V₁ + U₂ * V₂ + U₃ * V₃ = -(Y * K)` (three-term symmetric product factorization),
2. `⟨U₁, L_A(V₁)⟩_F + ⟨U₂, L_A(V₂)⟩_F + ⟨U₃, L_A(V₃)⟩_F = ⟨Y, L_A(K)⟩_F`. -/
theorem byers_nash_three_term_bound [DecidableEq n]
    (A Y Y₁ Y₂ Y₃ K T₁ T₂ T₃ : Matrix n n ℝ)
    (hY : Y = Y₁ + Y₂ + Y₃)
    (hY₁ : Y₁ᵀ = -Y₁) (hY₂ : Y₂ᵀ = -Y₂) (hY₃ : Y₃ᵀ = -Y₃) (hK : Kᵀ = -K)
    (hT₁_symm : T₁ᵀ = T₁) (hT₁_inv : T₁ * T₁ = 1)
    (hT₂_symm : T₂ᵀ = T₂) (hT₂_inv : T₂ * T₂ = 1)
    (hT₃_symm : T₃ᵀ = T₃) (hT₃_inv : T₃ * T₃ = 1)
    (hT₁Y₁ : T₁ * Y₁ = -Y₁ * T₁) (hT₂Y₂ : T₂ * Y₂ = -Y₂ * T₂) (hT₃Y₃ : T₃ * Y₃ = -Y₃ * T₃)
    (hT₁K : T₁ * K = -K * T₁) (hT₂K : T₂ * K = -K * T₂) (hT₃K : T₃ * K = -K * T₃) :
    (Y₁ * T₁)ᵀ = Y₁ * T₁ ∧
    (Y₂ * T₂)ᵀ = Y₂ * T₂ ∧
    (Y₃ * T₃)ᵀ = Y₃ * T₃ ∧
    (Y₁ * T₁) * (K * T₁) + (Y₂ * T₂) * (K * T₂) + (Y₃ * T₃) * (K * T₃) = -(Y * K) ∧
    frobInner (Y₁ * T₁) (lyap A (K * T₁)) +
      frobInner (Y₂ * T₂) (lyap A (K * T₂)) +
      frobInner (Y₃ * T₃) (lyap A (K * T₃)) = frobInner Y (lyap A K) := by
  refine ⟨symm_of_skew_mul_anticomm Y₁ T₁ hY₁ hT₁_symm hT₁Y₁,
    symm_of_skew_mul_anticomm Y₂ T₂ hY₂ hT₂_symm hT₂Y₂,
    symm_of_skew_mul_anticomm Y₃ T₃ hY₃ hT₃_symm hT₃Y₃, ?_, ?_⟩
  · rw [common_involution_product_eq Y₁ K T₁ hT₁_inv hT₁K,
      common_involution_product_eq Y₂ K T₂ hT₂_inv hT₂K,
      common_involution_product_eq Y₃ K T₃ hT₃_inv hT₃K, hY]
    noncomm_ring
  · rw [common_involution_lyap_pairing A Y₁ K T₁ hY₁ hK hT₁_symm hT₁_inv hT₁Y₁ hT₁K,
      common_involution_lyap_pairing A Y₂ K T₂ hY₂ hK hT₂_symm hT₂_inv hT₂Y₂ hT₂K,
      common_involution_lyap_pairing A Y₃ K T₃ hY₃ hK hT₃_symm hT₃_inv hT₃Y₃ hT₃K,
      hY, frobInner_add_left, frobInner_add_left]

/-- **Multi-Involution Energy Identity (`byers_nash_orthogonal_involutions`)**:
For any four symmetric involutions `T₀, T₁, T₂, T₃` anticommuting with skew-symmetric `K`,
the sum of squared Frobenius gains `∑_{r=0}^3 ‖L_A(K T_r)‖_F²` equals
`4 ∑_{r=0}^3 ‖H_c(T_r)‖_F² + ∑_{r=0}^3 ‖Y_a(T_r)‖_F²`. -/
theorem byers_nash_orthogonal_involutions [DecidableEq n]
    (A K T₀ T₁ T₂ T₃ : Matrix n n ℝ) (hK : Kᵀ = -K)
    (hT₀_symm : T₀ᵀ = T₀) (hT₀_inv : T₀ * T₀ = 1) (hT₀K : T₀ * K = -K * T₀)
    (hT₁_symm : T₁ᵀ = T₁) (hT₁_inv : T₁ * T₁ = 1) (hT₁K : T₁ * K = -K * T₁)
    (hT₂_symm : T₂ᵀ = T₂) (hT₂_inv : T₂ * T₂ = 1) (hT₂K : T₂ * K = -K * T₂)
    (hT₃_symm : T₃ᵀ = T₃) (hT₃_inv : T₃ * T₃ = 1) (hT₃K : T₃ * K = -K * T₃) :
    frobNormSq (lyap A (K * T₀)) + frobNormSq (lyap A (K * T₁)) +
      frobNormSq (lyap A (K * T₂)) + frobNormSq (lyap A (K * T₃)) =
    4 * (frobNormSq (commPart T₀ (symPart A K)) + frobNormSq (commPart T₁ (symPart A K)) +
         frobNormSq (commPart T₂ (symPart A K)) + frobNormSq (commPart T₃ (symPart A K))) +
    (frobNormSq (anticommPart T₀ (lyap A K)) + frobNormSq (anticommPart T₁ (lyap A K)) +
     frobNormSq (anticommPart T₂ (lyap A K)) + frobNormSq (anticommPart T₃ (lyap A K))) := by
  have h0 := lyap_normSq_decomp_involution A K T₀ hK hT₀_symm hT₀_inv hT₀K
  have h1 := lyap_normSq_decomp_involution A K T₁ hK hT₁_symm hT₁_inv hT₁K
  have h2 := lyap_normSq_decomp_involution A K T₂ hK hT₂_symm hT₂_inv hT₂K
  have h3 := lyap_normSq_decomp_involution A K T₃ hK hT₃_symm hT₃_inv hT₃K
  linarith

/-! ## Section 3: Full-Rank $6 \times 6$ Darboux Normal Form & Klein 4-Group Involutions -/

abbrev Mat6 := Matrix (Fin 6) (Fin 6) ℝ

/-- The full-rank $6 \times 6$ Darboux normal form `K = diag(a J, b J, c J)`. -/
def skewWitness6 (a b c : ℝ) : Mat6 :=
  !![0, a, 0, 0, 0, 0;
    -a, 0, 0, 0, 0, 0;
     0, 0, 0, b, 0, 0;
     0, 0, -b, 0, 0, 0;
     0, 0, 0, 0, 0, c;
     0, 0, 0, 0, -c, 0]

/-- When `c = 0`, `skewWitness6 a b 0` reduces to the rank-4 `skewWitness a b`. -/
theorem skewWitness6_zero_eq_skewWitness (a b : ℝ) :
    skewWitness6 a b 0 = Research.SkewNormalForm.skewWitness a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, Research.SkewNormalForm.skewWitness]

/-- `skewWitness6 a b c` is skew-symmetric for all `a, b, c : ℝ`. -/
theorem skewWitness6_skew (a b c : ℝ) :
    (skewWitness6 a b c)ᵀ = -skewWitness6 a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, Matrix.transpose_apply]

/-- Diagonal sign vectors for the Klein 4-group involutions `T0, T1, T2, T3`. -/
def d0 : Fin 6 → ℝ := ![1, -1, 1, -1, 1, -1]
def d1 : Fin 6 → ℝ := ![1, -1, -1, 1, -1, 1]
def d2 : Fin 6 → ℝ := ![-1, 1, 1, -1, -1, 1]
def d3 : Fin 6 → ℝ := ![-1, 1, -1, 1, 1, -1]

/-- The four Klein 4-group diagonal involutions `T0, T1, T2, T3` with $2\times 2$ block signs
`(+1,+1,+1)`, `(+1,-1,-1)`, `(-1,+1,-1)`, `(-1,-1,+1)` multiplying `F = diag(1, -1)`. -/
def T0 : Mat6 :=
  !![1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, -1]

def T1 : Mat6 :=
  !![1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 1]

def T2 : Mat6 :=
  !![-1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 1]

def T3 : Mat6 :=
  !![-1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, -1]

theorem T0_symm : T0ᵀ = T0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T0, Matrix.transpose_apply]

theorem T1_symm : T1ᵀ = T1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T1, Matrix.transpose_apply]

theorem T2_symm : T2ᵀ = T2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T2, Matrix.transpose_apply]

theorem T3_symm : T3ᵀ = T3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T3, Matrix.transpose_apply]

theorem T0_inv : T0 * T0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T0, Matrix.mul_apply, Fin.sum_univ_succ]

theorem T1_inv : T1 * T1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T1, Matrix.mul_apply, Fin.sum_univ_succ]

theorem T2_inv : T2 * T2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem T3_inv : T3 * T3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Fast diagonal multiplication and conjugation formulas for `T0, T1, T2, T3`. -/
lemma T0_mul_apply (Y : Mat6) (i j : Fin 6) :
    (T0 * Y) i j = d0 i * Y i j := by
  fin_cases i <;>
    simp [T0, d0, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_T0_apply (Y : Mat6) (i j : Fin 6) :
    (Y * T0) i j = Y i j * d0 j := by
  fin_cases j <;>
    simp [T0, d0, Matrix.mul_apply, Fin.sum_univ_succ]

lemma T0_conj_apply (Y : Mat6) (i j : Fin 6) :
    (T0 * Y * T0) i j = d0 i * Y i j * d0 j := by
  rw [mul_T0_apply, T0_mul_apply]

lemma T1_mul_apply (Y : Mat6) (i j : Fin 6) :
    (T1 * Y) i j = d1 i * Y i j := by
  fin_cases i <;>
    simp [T1, d1, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_T1_apply (Y : Mat6) (i j : Fin 6) :
    (Y * T1) i j = Y i j * d1 j := by
  fin_cases j <;>
    simp [T1, d1, Matrix.mul_apply, Fin.sum_univ_succ]

lemma T1_conj_apply (Y : Mat6) (i j : Fin 6) :
    (T1 * Y * T1) i j = d1 i * Y i j * d1 j := by
  rw [mul_T1_apply, T1_mul_apply]

lemma T2_mul_apply (Y : Mat6) (i j : Fin 6) :
    (T2 * Y) i j = d2 i * Y i j := by
  fin_cases i <;>
    simp [T2, d2, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_T2_apply (Y : Mat6) (i j : Fin 6) :
    (Y * T2) i j = Y i j * d2 j := by
  fin_cases j <;>
    simp [T2, d2, Matrix.mul_apply, Fin.sum_univ_succ]

lemma T2_conj_apply (Y : Mat6) (i j : Fin 6) :
    (T2 * Y * T2) i j = d2 i * Y i j * d2 j := by
  rw [mul_T2_apply, T2_mul_apply]

lemma T3_mul_apply (Y : Mat6) (i j : Fin 6) :
    (T3 * Y) i j = d3 i * Y i j := by
  fin_cases i <;>
    simp [T3, d3, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_T3_apply (Y : Mat6) (i j : Fin 6) :
    (Y * T3) i j = Y i j * d3 j := by
  fin_cases j <;>
    simp [T3, d3, Matrix.mul_apply, Fin.sum_univ_succ]

lemma T3_conj_apply (Y : Mat6) (i j : Fin 6) :
    (T3 * Y * T3) i j = d3 i * Y i j * d3 j := by
  rw [mul_T3_apply, T3_mul_apply]

/-- All four Klein 4-group involutions `T0, T1, T2, T3` anticommute with `skewWitness6 a b c`. -/
theorem T0_anticomm_skewWitness6 (a b c : ℝ) :
    T0 * skewWitness6 a b c = -skewWitness6 a b c * T0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T0, skewWitness6, Matrix.mul_apply, Fin.sum_univ_succ]

theorem T1_anticomm_skewWitness6 (a b c : ℝ) :
    T1 * skewWitness6 a b c = -skewWitness6 a b c * T1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T1, skewWitness6, Matrix.mul_apply, Fin.sum_univ_succ]

theorem T2_anticomm_skewWitness6 (a b c : ℝ) :
    T2 * skewWitness6 a b c = -skewWitness6 a b c * T2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T2, skewWitness6, Matrix.mul_apply, Fin.sum_univ_succ]

theorem T3_anticomm_skewWitness6 (a b c : ℝ) :
    T3 * skewWitness6 a b c = -skewWitness6 a b c * T3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [T3, skewWitness6, Matrix.mul_apply, Fin.sum_univ_succ]

/-- For ANY symmetric involution `T` anticommuting with skew-symmetric `K`,
the symmetric comparator `S = K * T` satisfies `Sᵀ = S`, `S * S = -K * K`, and
`‖S‖_F² = ‖K‖_F²`. -/
theorem same_square_of_anticomm_involution [DecidableEq n] (K T : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) (hTK : T * K = -K * T) :
    (K * T)ᵀ = K * T ∧
    (K * T) * (K * T) = -(K * K) ∧
    frobNormSq (K * T) = frobNormSq K := by
  refine ⟨symm_of_skew_mul_anticomm K T hK hT_symm hTK,
    common_involution_product_eq K K T hT_inv hTK,
    frobNormSq_mul_symm_involution K T hT_symm hT_inv⟩

/-- All four symmetric comparators `S_r = skewWitness6 a b c * T_r` (`r = 0, 1, 2, 3`)
are symmetric, have the exact same square `-K²`, and the exact same Frobenius norm as `K`. -/
theorem four_involutions_same_square (a b c : ℝ) :
    let K := skewWitness6 a b c
    ((K * T0)ᵀ = K * T0 ∧ (K * T0) * (K * T0) = -(K * K) ∧ frobNormSq (K * T0) = frobNormSq K) ∧
    ((K * T1)ᵀ = K * T1 ∧ (K * T1) * (K * T1) = -(K * K) ∧ frobNormSq (K * T1) = frobNormSq K) ∧
    ((K * T2)ᵀ = K * T2 ∧ (K * T2) * (K * T2) = -(K * K) ∧ frobNormSq (K * T2) = frobNormSq K) ∧
    ((K * T3)ᵀ = K * T3 ∧ (K * T3) * (K * T3) = -(K * K) ∧ frobNormSq (K * T3) = frobNormSq K) := by
  intro K
  have hK := skewWitness6_skew a b c
  exact ⟨same_square_of_anticomm_involution K T0 hK T0_symm T0_inv (T0_anticomm_skewWitness6 a b c),
    same_square_of_anticomm_involution K T1 hK T1_symm T1_inv (T1_anticomm_skewWitness6 a b c),
    same_square_of_anticomm_involution K T2 hK T2_symm T2_inv (T2_anticomm_skewWitness6 a b c),
    same_square_of_anticomm_involution K T3 hK T3_symm T3_inv (T3_anticomm_skewWitness6 a b c)⟩

/-! ## Section 4: Block Decomposition of $6 \times 6$ Matrices & Character Table Identities -/

/-- The plane index `0, 1, 2` of each coordinate `i : Fin 6`, grouping `{0,1}`, `{2,3}`, `{4,5}`. -/
def planeOf (i : Fin 6) : ℕ :=
  i.val / 2

/-- Projection onto the three $2 \times 2$ diagonal blocks $\Pi_1, \Pi_2, \Pi_3$. -/
def diagBlocks (Y : Mat6) : Mat6 :=
  Matrix.of (fun i j => if planeOf i = planeOf j then Y i j else 0)

/-- Projection onto the off-diagonal $2 \times 2$ blocks ($\Pi_p \times \Pi_q$ for $p \ne q$). -/
def offDiagBlocks (Y : Mat6) : Mat6 :=
  Matrix.of (fun i j => if planeOf i = planeOf j then 0 else Y i j)

/-- Projection onto the $(1, 2)$ and $(2, 1)$ off-diagonal block pair. -/
def blockPair12 (Y : Mat6) : Mat6 :=
  Matrix.of (fun i j =>
    if (planeOf i = 0 ∧ planeOf j = 1) ∨ (planeOf i = 1 ∧ planeOf j = 0) then Y i j else 0)

/-- Projection onto the $(1, 3)$ and $(3, 1)$ off-diagonal block pair. -/
def blockPair13 (Y : Mat6) : Mat6 :=
  Matrix.of (fun i j =>
    if (planeOf i = 0 ∧ planeOf j = 2) ∨ (planeOf i = 2 ∧ planeOf j = 0) then Y i j else 0)

/-- Projection onto the $(2, 3)$ and $(3, 2)$ off-diagonal block pair. -/
def blockPair23 (Y : Mat6) : Mat6 :=
  Matrix.of (fun i j =>
    if (planeOf i = 1 ∧ planeOf j = 2) ∨ (planeOf i = 2 ∧ planeOf j = 1) then Y i j else 0)

/-- Every $6 \times 6$ matrix decomposes into `diagBlocks Y + offDiagBlocks Y`. -/
theorem diagBlocks_add_offDiagBlocks (Y : Mat6) :
    diagBlocks Y + offDiagBlocks Y = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagBlocks, offDiagBlocks, planeOf]

/-- The off-diagonal part decomposes into the three plane-pair components. -/
theorem offDiagBlocks_eq_sum_pairs (Y : Mat6) :
    offDiagBlocks Y = blockPair12 Y + blockPair13 Y + blockPair23 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagBlocks, blockPair12, blockPair13, blockPair23, planeOf]

/-- Complete 4-part block decomposition of any $6 \times 6$ matrix. -/
theorem block_four_part_decomposition (Y : Mat6) :
    Y = diagBlocks Y + blockPair12 Y + blockPair13 Y + blockPair23 Y := by
  calc
    Y = diagBlocks Y + offDiagBlocks Y := (diagBlocks_add_offDiagBlocks Y).symm
    _ = diagBlocks Y + (blockPair12 Y + blockPair13 Y + blockPair23 Y) := by
      rw [offDiagBlocks_eq_sum_pairs]
    _ = diagBlocks Y + blockPair12 Y + blockPair13 Y + blockPair23 Y := by abel

/-- `diagBlocks Y` and `offDiagBlocks Z` are Frobenius-orthogonal. -/
theorem frobInner_diagBlocks_offDiagBlocks (Y Z : Mat6) :
    frobInner (diagBlocks Y) (offDiagBlocks Z) = 0 := by
  unfold frobInner diagBlocks offDiagBlocks
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fin.sum_univ_six, planeOf]
  norm_num

/-- `offDiagBlocks Z` and `diagBlocks Y` are Frobenius-orthogonal. -/
theorem frobInner_offDiagBlocks_diagBlocks (Z Y : Mat6) :
    frobInner (offDiagBlocks Z) (diagBlocks Y) = 0 := by
  rw [frobInner_comm]
  exact frobInner_diagBlocks_offDiagBlocks Y Z

/-- Pythagorean norm decomposition `‖Y‖_F² = ‖diagBlocks Y‖_F² + ‖offDiagBlocks Y‖_F²`. -/
theorem frobNormSq_eq_diagBlocks_add_offDiagBlocks (Y : Mat6) :
    frobNormSq Y = frobNormSq (diagBlocks Y) + frobNormSq (offDiagBlocks Y) := by
  conv_lhs => rw [← diagBlocks_add_offDiagBlocks Y]
  exact frobNormSq_add_of_frobInner_eq_zero (diagBlocks Y) (offDiagBlocks Y)
    (frobInner_diagBlocks_offDiagBlocks Y Y)

lemma diagBlocks_skew (Y : Mat6) (hY : Yᵀ = -Y) :
    (diagBlocks Y)ᵀ = -diagBlocks Y := by
  ext i j
  have hij := congr_fun (congr_fun hY j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  fin_cases i <;> fin_cases j <;>
    simp [diagBlocks, planeOf] at hij ⊢ <;> linarith

lemma diagBlocks_comm_skewWitness6 (Y : Mat6) (hY : Yᵀ = -Y) (a b c : ℝ) :
    diagBlocks Y * skewWitness6 a b c = skewWitness6 a b c * diagBlocks Y := by
  have h00 : Y 0 0 = 0 := by have := congr_fun (congr_fun hY 0) 0; simp [Matrix.transpose_apply] at this; linarith
  have h11 : Y 1 1 = 0 := by have := congr_fun (congr_fun hY 1) 1; simp [Matrix.transpose_apply] at this; linarith
  have h22 : Y 2 2 = 0 := by have := congr_fun (congr_fun hY 2) 2; simp [Matrix.transpose_apply] at this; linarith
  have h33 : Y 3 3 = 0 := by have := congr_fun (congr_fun hY 3) 3; simp [Matrix.transpose_apply] at this; linarith
  have h44 : Y 4 4 = 0 := by have := congr_fun (congr_fun hY 4) 4; simp [Matrix.transpose_apply] at this; linarith
  have h55 : Y 5 5 = 0 := by have := congr_fun (congr_fun hY 5) 5; simp [Matrix.transpose_apply] at this; linarith
  have h10 : Y 1 0 = -Y 0 1 := by have := congr_fun (congr_fun hY 0) 1; simp [Matrix.transpose_apply] at this; linarith
  have h32 : Y 3 2 = -Y 2 3 := by have := congr_fun (congr_fun hY 2) 3; simp [Matrix.transpose_apply] at this; linarith
  have h54 : Y 5 4 = -Y 4 5 := by have := congr_fun (congr_fun hY 4) 5; simp [Matrix.transpose_apply] at this; linarith
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagBlocks, planeOf, skewWitness6, Matrix.mul_apply, Fin.sum_univ_succ,
      h00, h11, h22, h33, h44, h55, h10, h32, h54] <;> ring

lemma T0_anticomm_diagBlocks (Y : Mat6) (hY : Yᵀ = -Y) :
    T0 * diagBlocks Y = -diagBlocks Y * T0 := by
  ext i j
  have hij := congr_fun (congr_fun hY j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  rw [T0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T0_apply]
  fin_cases i <;> fin_cases j <;>
    simp [d0, diagBlocks, planeOf] at hij ⊢ <;> linarith

lemma T1_anticomm_diagBlocks (Y : Mat6) (hY : Yᵀ = -Y) :
    T1 * diagBlocks Y = -diagBlocks Y * T1 := by
  ext i j
  have hij := congr_fun (congr_fun hY j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  rw [T1_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T1_apply]
  fin_cases i <;> fin_cases j <;>
    simp [d1, diagBlocks, planeOf] at hij ⊢ <;> linarith

lemma T2_anticomm_diagBlocks (Y : Mat6) (hY : Yᵀ = -Y) :
    T2 * diagBlocks Y = -diagBlocks Y * T2 := by
  ext i j
  have hij := congr_fun (congr_fun hY j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  rw [T2_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T2_apply]
  fin_cases i <;> fin_cases j <;>
    simp [d2, diagBlocks, planeOf] at hij ⊢ <;> linarith

lemma T3_anticomm_diagBlocks (Y : Mat6) (hY : Yᵀ = -Y) :
    T3 * diagBlocks Y = -diagBlocks Y * T3 := by
  ext i j
  have hij := congr_fun (congr_fun hY j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  rw [T3_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T3_apply]
  fin_cases i <;> fin_cases j <;>
    simp [d3, diagBlocks, planeOf] at hij ⊢ <;> linarith

/-- If `Y` is skew-symmetric, `diagBlocks Y` is skew-symmetric, commutes with `skewWitness6 a b c`,
and strictly anticommutes with all four Klein 4-group involutions `T0, T1, T2, T3`. -/
theorem diagBlocks_skew_properties (Y : Mat6) (hY : Yᵀ = -Y) (a b c : ℝ) :
    (diagBlocks Y)ᵀ = -diagBlocks Y ∧
    diagBlocks Y * skewWitness6 a b c = skewWitness6 a b c * diagBlocks Y ∧
    T0 * diagBlocks Y = -diagBlocks Y * T0 ∧
    T1 * diagBlocks Y = -diagBlocks Y * T1 ∧
    T2 * diagBlocks Y = -diagBlocks Y * T2 ∧
    T3 * diagBlocks Y = -diagBlocks Y * T3 :=
  ⟨diagBlocks_skew Y hY,
   diagBlocks_comm_skewWitness6 Y hY a b c,
   T0_anticomm_diagBlocks Y hY,
   T1_anticomm_diagBlocks Y hY,
   T2_anticomm_diagBlocks Y hY,
   T3_anticomm_diagBlocks Y hY⟩

/-- **Klein 4-Group Character Projection Theorem**:
1. Averaging `T_r Y T_r` over `r ∈ {0, 1, 2, 3}` projects any $6 \times 6$ matrix `Y` onto
   `T0 * diagBlocks Y * T0`.
2. Weighting by the three non-trivial characters of the Klein 4-group isolates
   `T0 * blockPair12 Y * T0`, `T0 * blockPair13 Y * T0`, and `T0 * blockPair23 Y * T0`. -/
theorem klein_four_character_projections (Y : Mat6) :
    (1 / 4 : ℝ) • (T0 * Y * T0 + T1 * Y * T1 + T2 * Y * T2 + T3 * Y * T3) =
      T0 * diagBlocks Y * T0 ∧
    (1 / 4 : ℝ) • (T0 * Y * T0 - T1 * Y * T1 - T2 * Y * T2 + T3 * Y * T3) =
      T0 * blockPair12 Y * T0 ∧
    (1 / 4 : ℝ) • (T0 * Y * T0 - T1 * Y * T1 + T2 * Y * T2 - T3 * Y * T3) =
      T0 * blockPair13 Y * T0 ∧
    (1 / 4 : ℝ) • (T0 * Y * T0 + T1 * Y * T1 - T2 * Y * T2 - T3 * Y * T3) =
      T0 * blockPair23 Y * T0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, T0_conj_apply, T1_conj_apply,
      T2_conj_apply, T3_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d1, d2, d3, diagBlocks, planeOf] <;> ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, T0_conj_apply,
      T1_conj_apply, T2_conj_apply, T3_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d1, d2, d3, blockPair12, planeOf] <;> ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, T0_conj_apply,
      T1_conj_apply, T2_conj_apply, T3_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d1, d2, d3, blockPair13, planeOf] <;> ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, T0_conj_apply,
      T1_conj_apply, T2_conj_apply, T3_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d1, d2, d3, blockPair23, planeOf] <;> ring

/-- For skew-symmetric `Y`, the Klein 4-group average `(1/4) ∑_{r=0}^3 T_r Y T_r` equals `-diagBlocks Y`. -/
theorem klein_four_average_skew (Y : Mat6) (hY : Yᵀ = -Y) :
    (1 / 4 : ℝ) • (T0 * Y * T0 + T1 * Y * T1 + T2 * Y * T2 + T3 * Y * T3) =
      -diagBlocks Y := by
  rw [(klein_four_character_projections Y).1]
  have hanti := T0_anticomm_diagBlocks Y hY
  calc
    T0 * diagBlocks Y * T0 = (-diagBlocks Y * T0) * T0 := by rw [hanti]
    _ = -diagBlocks Y * (T0 * T0) := Matrix.mul_assoc (-diagBlocks Y) T0 T0
    _ = -diagBlocks Y := by rw [T0_inv, Matrix.mul_one]

/-- Pairwise character combinations `-(1/2)(T0 Y T0 + T_r Y T_r)` for skew-symmetric `Y`. -/
theorem klein_four_pairwise_projections_skew (Y : Mat6) (hY : Yᵀ = -Y) :
    -(1 / 2 : ℝ) • (T0 * Y * T0 + T1 * Y * T1) = diagBlocks Y - T0 * blockPair23 Y * T0 ∧
    -(1 / 2 : ℝ) • (T0 * Y * T0 + T2 * Y * T2) = diagBlocks Y - T0 * blockPair13 Y * T0 ∧
    -(1 / 2 : ℝ) • (T0 * Y * T0 + T3 * Y * T3) = diagBlocks Y - T0 * blockPair12 Y * T0 := by
  have hanti : T0 * diagBlocks Y * T0 = -diagBlocks Y := by
    rw [← (klein_four_character_projections Y).1, klein_four_average_skew Y hY]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have h_diag := congr_fun (congr_fun hanti i) j
    simp only [T0_conj_apply, Matrix.neg_apply] at h_diag
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      T0_conj_apply, T1_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d1, diagBlocks, blockPair23, planeOf] at h_diag ⊢ <;> linarith
  · ext i j
    have h_diag := congr_fun (congr_fun hanti i) j
    simp only [T0_conj_apply, Matrix.neg_apply] at h_diag
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      T0_conj_apply, T2_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d2, diagBlocks, blockPair13, planeOf] at h_diag ⊢ <;> linarith
  · ext i j
    have h_diag := congr_fun (congr_fun hanti i) j
    simp only [T0_conj_apply, Matrix.neg_apply] at h_diag
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      T0_conj_apply, T3_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d0, d3, diagBlocks, blockPair12, planeOf] at h_diag ⊢ <;> linarith

/-! ## Section 5: Four-Involution Parseval / Character Decomposition Theorem -/

/-- Exact norm identity for `commPart T X` and `anticommPart T X` in terms of `⟨X, T X T⟩_F`. -/
theorem frobNormSq_commPart_anticommPart_eq [DecidableEq n] (T X : Matrix n n ℝ)
    (hT_symm : Tᵀ = T) (hT_inv : T * T = 1) :
    frobNormSq (commPart T X) = (1 / 2 : ℝ) * frobNormSq X + (1 / 2 : ℝ) * frobInner X (T * X * T) ∧
    frobNormSq (anticommPart T X) = (1 / 2 : ℝ) * frobNormSq X - (1 / 2 : ℝ) * frobInner X (T * X * T) := by
  have h_norm : frobInner (T * X * T) (T * X * T) = frobInner X X :=
    frobInner_conj_symm_involution X X T hT_symm hT_inv
  have h_comm : frobInner (T * X * T) X = frobInner X (T * X * T) :=
    frobInner_comm (T * X * T) X
  unfold commPart anticommPart frobNormSq frobInner
  unfold frobInner at h_norm h_comm
  constructor
  · rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul,
      transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      trace_add, trace_add, trace_add]
    simp only [smul_eq_mul]
    linarith
  · rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul,
      transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      trace_sub, trace_sub, trace_sub]
    simp only [smul_eq_mul]
    linarith

/-- For any skew-symmetric $6 \times 6$ matrix `Y`, the Klein 4-group Parseval identities hold:
1. `∑_{r=0}^3 ‖commPart T_r Y‖_F² = 2 ‖offDiagBlocks Y‖_F²`,
2. `∑_{r=0}^3 ‖anticommPart T_r Y‖_F² = 2 ‖Y‖_F² + 2 ‖diagBlocks Y‖_F² = 4 ‖diagBlocks Y‖_F² + 2 ‖offDiagBlocks Y‖_F²`. -/
theorem klein_four_parseval_skew (Y : Mat6) (hY : Yᵀ = -Y) :
    frobNormSq (commPart T0 Y) + frobNormSq (commPart T1 Y) +
      frobNormSq (commPart T2 Y) + frobNormSq (commPart T3 Y) =
        2 * frobNormSq (offDiagBlocks Y) ∧
    frobNormSq (anticommPart T0 Y) + frobNormSq (anticommPart T1 Y) +
      frobNormSq (anticommPart T2 Y) + frobNormSq (anticommPart T3 Y) =
        2 * frobNormSq Y + 2 * frobNormSq (diagBlocks Y) := by
  have h0 := frobNormSq_commPart_anticommPart_eq T0 Y T0_symm T0_inv
  have h1 := frobNormSq_commPart_anticommPart_eq T1 Y T1_symm T1_inv
  have h2 := frobNormSq_commPart_anticommPart_eq T2 Y T2_symm T2_inv
  have h3 := frobNormSq_commPart_anticommPart_eq T3 Y T3_symm T3_inv
  have h_avg := klein_four_average_skew Y hY
  have h_sum_inner :
      frobInner Y (T0 * Y * T0) + frobInner Y (T1 * Y * T1) +
        frobInner Y (T2 * Y * T2) + frobInner Y (T3 * Y * T3) =
      -4 * frobNormSq (diagBlocks Y) := by
    have h_lin :
        frobInner Y (T0 * Y * T0) + frobInner Y (T1 * Y * T1) +
          frobInner Y (T2 * Y * T2) + frobInner Y (T3 * Y * T3) =
        4 * frobInner Y ((1 / 4 : ℝ) • (T0 * Y * T0 + T1 * Y * T1 + T2 * Y * T2 + T3 * Y * T3)) := by
      unfold frobInner
      rw [Matrix.mul_smul, trace_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        trace_add, trace_add, trace_add]
      simp only [smul_eq_mul]
      ring
    rw [h_lin, h_avg]
    have h_split : frobInner (diagBlocks Y + offDiagBlocks Y) (-diagBlocks Y) =
        -frobNormSq (diagBlocks Y) := by
      calc
        frobInner (diagBlocks Y + offDiagBlocks Y) (-diagBlocks Y)
          = frobInner (diagBlocks Y) (-diagBlocks Y) +
              frobInner (offDiagBlocks Y) (-diagBlocks Y) :=
            frobInner_add_left (diagBlocks Y) (offDiagBlocks Y) (-diagBlocks Y)
        _ = -frobNormSq (diagBlocks Y) - frobInner (offDiagBlocks Y) (diagBlocks Y) := by
          unfold frobNormSq frobInner
          rw [Matrix.mul_neg, trace_neg, Matrix.mul_neg, trace_neg]
          ring
        _ = -frobNormSq (diagBlocks Y) := by
          rw [frobInner_offDiagBlocks_diagBlocks Y Y]
          ring
    rw [diagBlocks_add_offDiagBlocks Y] at h_split
    linarith
  have h_pyth := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  constructor
  · linarith [h0.1, h1.1, h2.1, h3.1, h_sum_inner, h_pyth]
  · linarith [h0.2, h1.2, h2.2, h3.2, h_sum_inner]

/-- **Main Theorem: Four-Involution Parseval / Character Decomposition (`four_involution_parseval_decomposition`)**:
For any $6 \times 6$ system matrix `A` and any full-rank Darboux skew matrix `K = skewWitness6 a b c`:
1. The sum of squared Frobenius gains over the four Klein 4-group comparators `S_r = K * T_r` satisfies
   $$\sum_{r=0}^3 \|\mathcal{L}_A(K T_r)\|_F^2
     = 4 \sum_{r=0}^3 \|H_c(T_r)\|_F^2 + 2 \|\mathcal{L}_A(K)\|_F^2 + 2 \|\operatorname{diagBlocks}(\mathcal{L}_A(K))\|_F^2.$$
2. Consequently,
   $$\sum_{r=0}^3 \|\mathcal{L}_A(K T_r)\|_F^2
     \ge 2 \|\mathcal{L}_A(K)\|_F^2 + 2 \|\operatorname{diagBlocks}(\mathcal{L}_A(K))\|_F^2.$$
3. At least one of the four symmetric comparators `S_r = K * T_r` ($r \in \{0, 1, 2, 3\}$) satisfies
   $$\|\mathcal{L}_A(S_r)\|_F^2 \ge \frac{1}{2} \|\mathcal{L}_A(K)\|_F^2 + \frac{1}{2} \|\operatorname{diagBlocks}(\mathcal{L}_A(K))\|_F^2.$$ -/
theorem four_involution_parseval_decomposition (A : Mat6) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    (frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
      frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) =
    4 * (frobNormSq (commPart T0 H) + frobNormSq (commPart T1 H) +
         frobNormSq (commPart T2 H) + frobNormSq (commPart T3 H)) +
    2 * frobNormSq Y + 2 * frobNormSq (diagBlocks Y)) ∧
    (2 * frobNormSq Y + 2 * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
        frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3))) ∧
    ((1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T0)) ∨
     (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T1)) ∨
     (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T2)) ∨
     (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T3))) := by
  intro K H Y
  have hK := skewWitness6_skew a b c
  have hY := lyap_skew_of_skew A K hK
  have h_orth := byers_nash_orthogonal_involutions A K T0 T1 T2 T3 hK
    T0_symm T0_inv (T0_anticomm_skewWitness6 a b c)
    T1_symm T1_inv (T1_anticomm_skewWitness6 a b c)
    T2_symm T2_inv (T2_anticomm_skewWitness6 a b c)
    T3_symm T3_inv (T3_anticomm_skewWitness6 a b c)
  have h_pars := (klein_four_parseval_skew Y hY).2
  have h_eq :
      frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
        frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) =
      4 * (frobNormSq (commPart T0 H) + frobNormSq (commPart T1 H) +
           frobNormSq (commPart T2 H) + frobNormSq (commPart T3 H)) +
      2 * frobNormSq Y + 2 * frobNormSq (diagBlocks Y) := by
    dsimp [H, Y]
    linarith [h_orth, h_pars]
  have h_nonneg (X : Mat6) : 0 ≤ frobNormSq X := by
    unfold frobNormSq frobInner
    rw [← Research.SkewNormalForm.frobeniusSquared_eq_trace]
    unfold Research.SkewNormalForm.frobeniusSquared
    positivity
  have h_H0 := h_nonneg (commPart T0 H)
  have h_H1 := h_nonneg (commPart T1 H)
  have h_H2 := h_nonneg (commPart T2 H)
  have h_H3 := h_nonneg (commPart T3 H)
  have h_ineq :
      2 * frobNormSq Y + 2 * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
          frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) := by
    linarith [h_eq, h_H0, h_H1, h_H2, h_H3]
  refine ⟨h_eq, h_ineq, ?_⟩
  by_cases h0 : (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T0))
  · exact Or.inl h0
  by_cases h1 : (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T1))
  · exact Or.inr (Or.inl h1)
  by_cases h2 : (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
      frobNormSq (lyap A (K * T2))
  · exact Or.inr (Or.inr (Or.inl h2))
  right; right; right
  linarith

#print axioms lyap_anticomm_pairing
#print axioms lyap_normSq_decomp_involution
#print axioms lyap_gain_diff_involution
#print axioms byers_nash_two_term_bound
#print axioms byers_nash_three_term_bound
#print axioms byers_nash_orthogonal_involutions
#print axioms four_involutions_same_square
#print axioms diagBlocks_skew_properties
#print axioms klein_four_character_projections
#print axioms klein_four_parseval_skew
#print axioms four_involution_parseval_decomposition

end Research.ByersNashMultiTerm
