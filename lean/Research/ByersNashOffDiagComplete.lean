import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Research.ByersNashHaarIntertwiner

/-!
# Off-Diagonal Plane-Swap Involutions, 15D Skew Parseval Theorem & Lyapunov Robustness

This module extends `Research.ByersNashHaarIntertwiner` with three main results completing
the harmonic analysis of $\mathbb{K}_6$ and the control-theoretic interpretation of the
Byers–Nash inequality $k(A) \le s(A)$:

1. **Off-Diagonal Plane-Swap Symmetric Involutions & Complete 15-Dimensional Skew Parseval
   Decomposition (`plane_swap_involutions_properties`, `skew6_fifteen_dim_parseval`,
   `equal_freq_f_swap_involutions_anticomm`)**:
   - Defines the three symmetric plane-swap orthogonal involutions `W12, W13, W23 : Mat6`
     exchanging Darboux planes `(1,2)`, `(1,3)`, and `(2,3)`.
   - For any skew-symmetric `Y ∈ 𝕂_6`, each 4-dimensional off-diagonal plane-pair component
     `blockPair_{pq} Y` decomposes orthogonally into its 3-dimensional `W_{pq}`-anticommuting
     part (`anticommPart W_{pq} (blockPair_{pq} Y)`, encoding the symmetric `{I₂, F, G}` block
     components) and its 1-dimensional `W_{pq}`-commuting part (`commPart W_{pq} (blockPair_{pq} Y)`,
     encoding the skew `J` block component), yielding the complete 15-dimensional Pythagorean
     decomposition of `𝕂_6`:
     `‖Y‖_F² = ‖diagBlocks Y‖_F² + ∑_{(p,q)} (‖anticommPart W_{pq} (blockPair_{pq} Y)‖_F² + ‖commPart W_{pq} (blockPair_{pq} Y)‖_F²)`.
   - Defines the three `F`-weighted plane-swap involutions `P12_F, P13_F, P23_F : Mat6` and
     proves that they are symmetric orthogonal involutions anticommuting with the equal-frequency
     Darboux normal forms `skewWitness6 a a c`, `skewWitness6 a b a`, and `skewWitness6 a b b`.

2. **Canonical 4-Term Norm Identity & Universal 12-Comparator Bound
   (`canonical_four_term_norm_identity`, `byers_nash_universal_12_comparator_bound`)**:
   - Proves that the four canonical symmetric left-partners `U_r = canonicalPiece T_r Y * T_r`
     (`r = 0, 1, 2, 3`) from `canonical_four_term_decomposition` satisfy the exact norm identity:
     `∑_{r=0}^3 ‖U_r‖_F² = (1/4) ‖diagBlocks Y‖_F² + (1/2) ‖offDiagBlocks Y‖_F² = (1/2) ‖Y‖_F² - (1/4) ‖diagBlocks Y‖_F²`.
   - Combines the 8 same-square comparators `{K T_r, K G_r}` with the 4 canonical dual
     comparators `{U_r}` to establish the universal 12-comparator energy identity and
     unconditional lower bound across both diagonal-dominated and off-diagonal-dominated regimes.

3. **Continuous-Time Lyapunov Orthogonal Decoupling & Robustness Bound
   (`lyap_symm_skew_orthogonal_decomp`, `lyapunov_singular_value_robustness_bound`)**:
   - Proves that for arbitrary dimension `n`, any matrix `X ∈ M_n(ℝ)` decomposes orthogonally
     into `matSymmPart X ∈ 𝕊_n` and `matSkewPart X ∈ 𝕂_n`, and their Lyapunov images
     `L_A(matSymmPart X) ∈ 𝕊_n` and `L_A(matSkewPart X) ∈ 𝕂_n` are Frobenius-orthogonal:
     `‖L_A(X)‖_F² = ‖L_A(matSymmPart X)‖_F² + ‖L_A(matSkewPart X)‖_F²`.
   - Consequently, an upper bound `‖L_A(S)‖_F² ≤ M² ‖S‖_F²` on `𝕊_n` together with the
     Byers–Nash dominance `‖L_A(matSkewPart X)‖_F² ≤ M² ‖matSkewPart X‖_F²` implies the
     global Kronecker-sum gain bound `‖L_A(X)‖_F² ≤ M² ‖X‖_F²` for all `X ∈ M_n(ℝ)`
     (and dually for lower singular value robustness bounds `σ² ‖X‖_F² ≤ ‖L_A(X)‖_F²`).
-/

namespace Research.ByersNashOffDiagComplete

open Matrix BigOperators
open Research.ByersNashDuality
open Research.ByersNashMultiTerm
open Research.ByersNashHaarIntertwiner

noncomputable section

/-! ## Section 1: Continuous-Time Lyapunov Orthogonal Decoupling & Robustness in Dimension `n` -/

variable {n : Type*}

/-- Symmetric part of a general `n × n` matrix: `matSymmPart X = (1/2) • (X + Xᵀ)`. -/
def matSymmPart (X : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (X + Xᵀ)

/-- Skew-symmetric part of a general `n × n` matrix: `matSkewPart X = (1/2) • (X - Xᵀ)`. -/
def matSkewPart (X : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (X - Xᵀ)

lemma matSymmPart_transpose (X : Matrix n n ℝ) :
    (matSymmPart X)ᵀ = matSymmPart X := by
  unfold matSymmPart
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

lemma matSkewPart_transpose (X : Matrix n n ℝ) :
    (matSkewPart X)ᵀ = -matSkewPart X := by
  unfold matSkewPart
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

lemma matSymmPart_add_matSkewPart (X : Matrix n n ℝ) :
    matSymmPart X + matSkewPart X = X := by
  unfold matSymmPart matSkewPart
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma lyap_symm_of_symm [Fintype n] (A S : Matrix n n ℝ) (hS : Sᵀ = S) :
    (lyap A S)ᵀ = lyap A S := by
  unfold lyap
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hS, add_comm]

lemma lyap_add_right [Fintype n] (A X Y : Matrix n n ℝ) :
    lyap A (X + Y) = lyap A X + lyap A Y := by
  unfold lyap
  noncomm_ring

/-- **Lyapunov Symmetric–Skew Orthogonal Decoupling Theorem**:
For every `A, X : Matrix n n ℝ`:
1. `‖X‖_F² = ‖matSymmPart X‖_F² + ‖matSkewPart X‖_F²`.
2. `L_A(matSymmPart X)` is symmetric and `L_A(matSkewPart X)` is skew-symmetric, hence
   `⟨L_A(matSymmPart X), L_A(matSkewPart X)⟩_F = 0`.
3. `‖L_A(X)‖_F² = ‖L_A(matSymmPart X)‖_F² + ‖L_A(matSkewPart X)‖_F²`. -/
theorem lyap_symm_skew_orthogonal_decomp [Fintype n] (A X : Matrix n n ℝ) :
    frobNormSq X = frobNormSq (matSymmPart X) + frobNormSq (matSkewPart X) ∧
    frobInner (lyap A (matSymmPart X)) (lyap A (matSkewPart X)) = 0 ∧
    frobNormSq (lyap A X) =
      frobNormSq (lyap A (matSymmPart X)) + frobNormSq (lyap A (matSkewPart X)) := by
  have hS := matSymmPart_transpose X
  have hK := matSkewPart_transpose X
  have hOrthX : frobInner (matSymmPart X) (matSkewPart X) = 0 :=
    frobInner_symm_skew_eq_zero (matSymmPart X) (matSkewPart X) hS hK
  have hNormX : frobNormSq X = frobNormSq (matSymmPart X) + frobNormSq (matSkewPart X) := by
    conv_lhs => rw [← matSymmPart_add_matSkewPart X]
    exact frobNormSq_add_of_frobInner_eq_zero (matSymmPart X) (matSkewPart X) hOrthX
  have hLS := lyap_symm_of_symm A (matSymmPart X) hS
  have hLK := lyap_skew_of_skew A (matSkewPart X) hK
  have hOrthL : frobInner (lyap A (matSymmPart X)) (lyap A (matSkewPart X)) = 0 :=
    frobInner_symm_skew_eq_zero (lyap A (matSymmPart X)) (lyap A (matSkewPart X)) hLS hLK
  have hNormL :
      frobNormSq (lyap A X) =
        frobNormSq (lyap A (matSymmPart X)) + frobNormSq (lyap A (matSkewPart X)) := by
    conv_lhs => rw [← matSymmPart_add_matSkewPart X, lyap_add_right]
    exact frobNormSq_add_of_frobInner_eq_zero (lyap A (matSymmPart X)) (lyap A (matSkewPart X)) hOrthL
  exact ⟨hNormX, hOrthL, hNormL⟩

/-- **Continuous-Time Lyapunov Singular Value & Gain Robustness Bound**:
Because `L_A` decouples orthogonally across `𝕊_n ⊕ 𝕂_n`, if the symmetric and skew-symmetric
components of `X ∈ M_n(ℝ)` satisfy upper gain bounds `≤ M²` (resp. lower singular value
bounds `≥ σ²`), then the full matrix `X` satisfies the exact same bound:
`σ² ‖X‖_F² ≤ ‖L_A(X)‖_F² ≤ M² ‖X‖_F²`. -/
theorem lyapunov_singular_value_robustness_bound [Fintype n]
    (A X : Matrix n n ℝ) (σSq MSq : ℝ)
    (hLowerSymm : σSq * frobNormSq (matSymmPart X) ≤ frobNormSq (lyap A (matSymmPart X)))
    (hLowerSkew : σSq * frobNormSq (matSkewPart X) ≤ frobNormSq (lyap A (matSkewPart X)))
    (hUpperSymm : frobNormSq (lyap A (matSymmPart X)) ≤ MSq * frobNormSq (matSymmPart X))
    (hUpperSkew : frobNormSq (lyap A (matSkewPart X)) ≤ MSq * frobNormSq (matSkewPart X)) :
    σSq * frobNormSq X ≤ frobNormSq (lyap A X) ∧
    frobNormSq (lyap A X) ≤ MSq * frobNormSq X := by
  have hDecomp := lyap_symm_skew_orthogonal_decomp A X
  rw [hDecomp.1, hDecomp.2.2, mul_add, mul_add]
  constructor <;> linarith

/-! ## Section 2: Off-Diagonal Plane-Swap Involutions & 15-Dimensional Skew Parseval Theorem -/

/-- Inter-plane swap permutations on `Fin 6` exchanging planes `(1,2)`, `(1,3)`, and `(2,3)`. -/
def perm12 : Fin 6 → Fin 6 := ![2, 3, 0, 1, 4, 5]
def perm13 : Fin 6 → Fin 6 := ![4, 5, 2, 3, 0, 1]
def perm23 : Fin 6 → Fin 6 := ![0, 1, 4, 5, 2, 3]

/-- Symmetric orthogonal plane-swap involutions `W12, W13, W23 : Mat6`. -/
def W12 : Mat6 := Matrix.of fun i j => if j = perm12 i then 1 else 0
def W13 : Mat6 := Matrix.of fun i j => if j = perm13 i then 1 else 0
def W23 : Mat6 := Matrix.of fun i j => if j = perm23 i then 1 else 0

lemma W12_mul_apply (X : Mat6) (i j : Fin 6) : (W12 * X) i j = X (perm12 i) j := by
  fin_cases i <;> simp [W12, perm12, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_W12_apply (X : Mat6) (i j : Fin 6) : (X * W12) i j = X i (perm12 j) := by
  fin_cases j <;> simp [W12, perm12, Matrix.mul_apply, Fin.sum_univ_succ]

lemma W12_conj_apply (X : Mat6) (i j : Fin 6) :
    (W12 * X * W12) i j = X (perm12 i) (perm12 j) := by
  rw [mul_W12_apply, W12_mul_apply]

lemma W13_mul_apply (X : Mat6) (i j : Fin 6) : (W13 * X) i j = X (perm13 i) j := by
  fin_cases i <;> simp [W13, perm13, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_W13_apply (X : Mat6) (i j : Fin 6) : (X * W13) i j = X i (perm13 j) := by
  fin_cases j <;> simp [W13, perm13, Matrix.mul_apply, Fin.sum_univ_succ]

lemma W13_conj_apply (X : Mat6) (i j : Fin 6) :
    (W13 * X * W13) i j = X (perm13 i) (perm13 j) := by
  rw [mul_W13_apply, W13_mul_apply]

lemma W23_mul_apply (X : Mat6) (i j : Fin 6) : (W23 * X) i j = X (perm23 i) j := by
  fin_cases i <;> simp [W23, perm23, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_W23_apply (X : Mat6) (i j : Fin 6) : (X * W23) i j = X i (perm23 j) := by
  fin_cases j <;> simp [W23, perm23, Matrix.mul_apply, Fin.sum_univ_succ]

lemma W23_conj_apply (X : Mat6) (i j : Fin 6) :
    (W23 * X * W23) i j = X (perm23 i) (perm23 j) := by
  rw [mul_W23_apply, W23_mul_apply]

lemma W12_symm : W12ᵀ = W12 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma W13_symm : W13ᵀ = W13 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma W23_symm : W23ᵀ = W23 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma W12_inv : W12 * W12 = 1 := by
  ext i j; rw [W12_mul_apply]; fin_cases i <;> fin_cases j <;> simp [W12, perm12]

lemma W13_inv : W13 * W13 = 1 := by
  ext i j; rw [W13_mul_apply]; fin_cases i <;> fin_cases j <;> simp [W13, perm13]

lemma W23_inv : W23 * W23 = 1 := by
  ext i j; rw [W23_mul_apply]; fin_cases i <;> fin_cases j <;> simp [W23, perm23]

/-- All three plane-swap matrices `W12, W13, W23` are symmetric orthogonal involutions. -/
theorem plane_swap_involutions_properties :
    W12ᵀ = W12 ∧ W13ᵀ = W13 ∧ W23ᵀ = W23 ∧
    W12 * W12 = 1 ∧ W13 * W13 = 1 ∧ W23 * W23 = 1 :=
  ⟨W12_symm, W13_symm, W23_symm, W12_inv, W13_inv, W23_inv⟩

/-- Canonical equal-frequency symplectic matrix `J6 = skewWitness6 1 1 1 = diag(J, J, J)`. -/
def J6 : Mat6 := skewWitness6 1 1 1

/-- Conjugation of `skewWitness6 a b c` by `W12, W13, W23` permutes the three Darboux frequencies
`(a, b, c)` by swapping `(a, b)`, `(a, c)`, and `(b, c)` respectively. -/
theorem plane_swap_conj_skewWitness6 (a b c : ℝ) :
    W12 * skewWitness6 a b c * W12 = skewWitness6 b a c ∧
    W13 * skewWitness6 a b c * W13 = skewWitness6 c b a ∧
    W23 * skewWitness6 a b c * W23 = skewWitness6 a c b := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; rw [W12_conj_apply]; fin_cases i <;> fin_cases j <;> simp [perm12, skewWitness6]
  · ext i j; rw [W13_conj_apply]; fin_cases i <;> fin_cases j <;> simp [perm13, skewWitness6]
  · ext i j; rw [W23_conj_apply]; fin_cases i <;> fin_cases j <;> simp [perm23, skewWitness6]

/-- `F`-weighted plane-swap involutions `P12_F`, `P13_F`, `P23_F`. -/
def P12_F : Mat6 := Matrix.of fun i j => if j = perm12 i then d0 i else 0
def P13_F : Mat6 := Matrix.of fun i j => if j = perm13 i then d0 i else 0
def P23_F : Mat6 := Matrix.of fun i j => if j = perm23 i then d0 i else 0

lemma P12_F_mul_apply (X : Mat6) (i j : Fin 6) : (P12_F * X) i j = d0 i * X (perm12 i) j := by
  fin_cases i <;> simp [P12_F, d0, perm12, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_P12_F_apply (X : Mat6) (i j : Fin 6) : (X * P12_F) i j = X i (perm12 j) * d0 j := by
  fin_cases j <;> simp [P12_F, d0, perm12, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P13_F_mul_apply (X : Mat6) (i j : Fin 6) : (P13_F * X) i j = d0 i * X (perm13 i) j := by
  fin_cases i <;> simp [P13_F, d0, perm13, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_P13_F_apply (X : Mat6) (i j : Fin 6) : (X * P13_F) i j = X i (perm13 j) * d0 j := by
  fin_cases j <;> simp [P13_F, d0, perm13, Matrix.mul_apply, Fin.sum_univ_succ]

lemma P23_F_mul_apply (X : Mat6) (i j : Fin 6) : (P23_F * X) i j = d0 i * X (perm23 i) j := by
  fin_cases i <;> simp [P23_F, d0, perm23, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_P23_F_apply (X : Mat6) (i j : Fin 6) : (X * P23_F) i j = X i (perm23 j) * d0 j := by
  fin_cases j <;> simp [P23_F, d0, perm23, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Plane-Swap Commutator Identity with `J6` and `skewWitness6 a b c` (`plane_swap_comm_J6`)**:
1. All three symmetric plane-swap involutions `W12, W13, W23` commute with `J6 = skewWitness6 1 1 1`.
2. All three `F`-weighted plane-swap involutions `P12_F, P13_F, P23_F` anticommute with `J6`.
3. For general `K = skewWitness6 a b c`, the commutators `W_{pq} * K - K * W_{pq}` are given by
   frequency-difference matrices multiplying `W_{pq}`. -/
theorem plane_swap_comm_J6 (a b c : ℝ) :
    W12 * J6 = J6 * W12 ∧
    W13 * J6 = J6 * W13 ∧
    W23 * J6 = J6 * W23 ∧
    P12_F * J6 = -J6 * P12_F ∧
    P13_F * J6 = -J6 * P13_F ∧
    P23_F * J6 = -J6 * P23_F ∧
    W12 * skewWitness6 a b c - skewWitness6 a b c * W12 =
      skewWitness6 (b - a) (a - b) 0 * W12 ∧
    W13 * skewWitness6 a b c - skewWitness6 a b c * W13 =
      skewWitness6 (c - a) 0 (a - c) * W13 ∧
    W23 * skewWitness6 a b c - skewWitness6 a b c * W23 =
      skewWitness6 0 (c - b) (b - c) * W23 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; rw [W12_mul_apply, mul_W12_apply]; fin_cases i <;> fin_cases j <;> simp [J6, perm12, skewWitness6]
  · ext i j; rw [W13_mul_apply, mul_W13_apply]; fin_cases i <;> fin_cases j <;> simp [J6, perm13, skewWitness6]
  · ext i j; rw [W23_mul_apply, mul_W23_apply]; fin_cases i <;> fin_cases j <;> simp [J6, perm23, skewWitness6]
  · ext i j; rw [P12_F_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_P12_F_apply]
    fin_cases i <;> fin_cases j <;> simp [J6, d0, perm12, skewWitness6]
  · ext i j; rw [P13_F_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_P13_F_apply]
    fin_cases i <;> fin_cases j <;> simp [J6, d0, perm13, skewWitness6]
  · ext i j; rw [P23_F_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_P23_F_apply]
    fin_cases i <;> fin_cases j <;> simp [J6, d0, perm23, skewWitness6]
  · ext i j
    simp only [Matrix.sub_apply, W12_mul_apply, mul_W12_apply]
    fin_cases i <;> fin_cases j <;> simp [perm12, skewWitness6] <;> ring
  · ext i j
    simp only [Matrix.sub_apply, W13_mul_apply, mul_W13_apply]
    fin_cases i <;> fin_cases j <;> simp [perm13, skewWitness6] <;> ring
  · ext i j
    simp only [Matrix.sub_apply, W23_mul_apply, mul_W23_apply]
    fin_cases i <;> fin_cases j <;> simp [perm23, skewWitness6] <;> ring

/-- The three `F`-weighted plane-swap matrices `P12_F, P13_F, P23_F` are symmetric orthogonal
involutions that anticommute with the equal-frequency Darboux matrices `skewWitness6 a a c`,
`skewWitness6 a b a`, and `skewWitness6 a b b` respectively. -/
theorem equal_freq_f_swap_involutions_anticomm (a b c : ℝ) :
    P12_Fᵀ = P12_F ∧ P13_Fᵀ = P13_F ∧ P23_Fᵀ = P23_F ∧
    P12_F * P12_F = 1 ∧ P13_F * P13_F = 1 ∧ P23_F * P23_F = 1 ∧
    P12_F * skewWitness6 a a c = -skewWitness6 a a c * P12_F ∧
    P13_F * skewWitness6 a b a = -skewWitness6 a b a * P13_F ∧
    P23_F * skewWitness6 a b b = -skewWitness6 a b b * P23_F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · ext i j; rw [P12_F_mul_apply]; fin_cases i <;> fin_cases j <;> simp [P12_F, d0, perm12]
  · ext i j; rw [P13_F_mul_apply]; fin_cases i <;> fin_cases j <;> simp [P13_F, d0, perm13]
  · ext i j; rw [P23_F_mul_apply]; fin_cases i <;> fin_cases j <;> simp [P23_F, d0, perm23]
  · ext i j
    rw [P12_F_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_P12_F_apply]
    fin_cases i <;> fin_cases j <;> simp [d0, perm12, skewWitness6]
  · ext i j
    rw [P13_F_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_P13_F_apply]
    fin_cases i <;> fin_cases j <;> simp [d0, perm13, skewWitness6]
  · ext i j
    rw [P23_F_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_P23_F_apply]
    fin_cases i <;> fin_cases j <;> simp [d0, perm23, skewWitness6]

/-- `offDiagBlocks Y` decomposes into the sum of the three disjoint plane-pair matrices. -/
theorem offDiagBlocks_eq_sum_blockPairs (Y : Mat6) :
    offDiagBlocks Y = blockPair12 Y + blockPair13 Y + blockPair23 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagBlocks, blockPair12, blockPair13, blockPair23, planeOf]

lemma frobInner_blockPair12_blockPair13 (X Y : Mat6) :
    frobInner (blockPair12 X) (blockPair13 Y) = 0 := by
  unfold frobInner blockPair12 blockPair13
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_six, planeOf]

lemma frobInner_blockPair12_blockPair23 (X Y : Mat6) :
    frobInner (blockPair12 X) (blockPair23 Y) = 0 := by
  unfold frobInner blockPair12 blockPair23
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_six, planeOf]

lemma frobInner_blockPair13_blockPair23 (X Y : Mat6) :
    frobInner (blockPair13 X) (blockPair23 Y) = 0 := by
  unfold frobInner blockPair13 blockPair23
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_six, planeOf]

/-- Pythagorean norm decomposition of `offDiagBlocks Y` across the three plane pairs `(1,2)`, `(1,3)`, `(2,3)`. -/
theorem frobNormSq_offDiagBlocks_eq_sum_blockPairs (Y : Mat6) :
    frobNormSq (offDiagBlocks Y) =
      frobNormSq (blockPair12 Y) + frobNormSq (blockPair13 Y) + frobNormSq (blockPair23 Y) := by
  have h12_13 := frobInner_blockPair12_blockPair13 Y Y
  have h12_23 := frobInner_blockPair12_blockPair23 Y Y
  have h13_23 := frobInner_blockPair13_blockPair23 Y Y
  have h123 : frobInner (blockPair12 Y + blockPair13 Y) (blockPair23 Y) = 0 := by
    rw [frobInner_add_left, h12_23, h13_23, add_zero]
  rw [offDiagBlocks_eq_sum_blockPairs Y,
      frobNormSq_add_of_frobInner_eq_zero (blockPair12 Y + blockPair13 Y) (blockPair23 Y) h123,
      frobNormSq_add_of_frobInner_eq_zero (blockPair12 Y) (blockPair13 Y) h12_13]

/-- **Complete 15-Dimensional Orthogonal Parseval Decomposition of `𝕂_6` (`skew6_fifteen_dim_parseval`)**:
Every `6 × 6` matrix `Y` decomposes orthogonally into `diagBlocks Y` (3D on `𝕂_6`) plus, for
each plane pair `(p,q) ∈ {(1,2), (1,3), (2,3)}`, its `W_{pq}`-anticommuting part (3D on `𝕂_6`,
encoding the symmetric `{I₂, F, G}` off-diagonal block components) and its `W_{pq}`-commuting
part (1D on `𝕂_6`, encoding the skew `J` off-diagonal block component):
`‖Y‖_F² = ‖diagBlocks Y‖_F² + ∑_{(p,q)} (‖anticommPart W_{pq} (blockPair_{pq} Y)‖_F² + ‖commPart W_{pq} (blockPair_{pq} Y)‖_F²)`. -/
theorem skew6_fifteen_dim_parseval (Y : Mat6) :
    Y = diagBlocks Y +
        (anticommPart W12 (blockPair12 Y) + commPart W12 (blockPair12 Y)) +
        (anticommPart W13 (blockPair13 Y) + commPart W13 (blockPair13 Y)) +
        (anticommPart W23 (blockPair23 Y) + commPart W23 (blockPair23 Y)) ∧
    frobNormSq Y =
      frobNormSq (diagBlocks Y) +
      (frobNormSq (anticommPart W12 (blockPair12 Y)) + frobNormSq (commPart W12 (blockPair12 Y))) +
      (frobNormSq (anticommPart W13 (blockPair13 Y)) + frobNormSq (commPart W13 (blockPair13 Y))) +
      (frobNormSq (anticommPart W23 (blockPair23 Y)) + frobNormSq (commPart W23 (blockPair23 Y))) := by
  have h12 := anticommPart_add_commPart W12 (blockPair12 Y)
  have h13 := anticommPart_add_commPart W13 (blockPair13 Y)
  have h23 := anticommPart_add_commPart W23 (blockPair23 Y)
  have hSum :
      Y = diagBlocks Y +
          (anticommPart W12 (blockPair12 Y) + commPart W12 (blockPair12 Y)) +
          (anticommPart W13 (blockPair13 Y) + commPart W13 (blockPair13 Y)) +
          (anticommPart W23 (blockPair23 Y) + commPart W23 (blockPair23 Y)) := by
    rw [h12, h13, h23]
    calc
      Y = diagBlocks Y + offDiagBlocks Y := (diagBlocks_add_offDiagBlocks Y).symm
      _ = diagBlocks Y + (blockPair12 Y + blockPair13 Y + blockPair23 Y) := by
        rw [offDiagBlocks_eq_sum_blockPairs Y]
      _ = diagBlocks Y + blockPair12 Y + blockPair13 Y + blockPair23 Y := by abel
  have hN12 := frobNormSq_eq_anticommPart_add_commPart W12 (blockPair12 Y) W12_symm W12_inv
  have hN13 := frobNormSq_eq_anticommPart_add_commPart W13 (blockPair13 Y) W13_symm W13_inv
  have hN23 := frobNormSq_eq_anticommPart_add_commPart W23 (blockPair23 Y) W23_symm W23_inv
  have hNDiag := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  have hNOff := frobNormSq_offDiagBlocks_eq_sum_blockPairs Y
  refine ⟨hSum, ?_⟩
  linarith [hNDiag, hNOff, hN12, hN13, hN23]

/-! ## Section 3: Canonical 4-Term Norm Identity & Universal 12-Comparator Bound -/

/-- For each Klein involution `T_r` (`r ∈ {0, 1, 2, 3}`) and skew-symmetric `Y ∈ 𝕂_6`,
the canonical piece `Y_r = canonicalPiece T_r Y` satisfies
`‖Y_r * T_r‖_F² = ‖Y_r‖_F² = (1/4) ‖anticommPart T_r Y‖_F² - (3/16) ‖diagBlocks Y‖_F²`. -/
lemma frobNormSq_canonicalPiece_eq
    (T Y : Mat6) (hT_symm : Tᵀ = T) (hT_inv : T * T = 1)
    (hDiag_anti : T * diagBlocks Y = -diagBlocks Y * T) :
    frobNormSq (canonicalPiece T Y * T) = frobNormSq (canonicalPiece T Y) ∧
    frobNormSq (canonicalPiece T Y) =
      (1 / 4 : ℝ) * frobNormSq (anticommPart T Y) -
        (3 / 16 : ℝ) * frobNormSq (diagBlocks Y) := by
  have hIso := frobNormSq_mul_symm_involution (canonicalPiece T Y) T hT_symm hT_inv
  refine ⟨hIso, ?_⟩
  have hT_diag : T * diagBlocks Y * T = -diagBlocks Y := by
    calc
      T * diagBlocks Y * T = (-diagBlocks Y * T) * T := by rw [hDiag_anti]
      _ = -diagBlocks Y * (T * T) := by noncomm_ring
      _ = -diagBlocks Y * 1 := by rw [hT_inv]
      _ = -diagBlocks Y := by rw [Matrix.mul_one]
  have hInner : frobInner (diagBlocks Y) (anticommPart T Y) = frobNormSq (diagBlocks Y) := by
    have hDecomp : Y = diagBlocks Y + offDiagBlocks Y := (diagBlocks_add_offDiagBlocks Y).symm
    have hAntiDiag : anticommPart T (diagBlocks Y) = diagBlocks Y := by
      unfold anticommPart
      rw [hT_diag]
      ext i j; simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]; ring
    have hOrthOff : frobInner (diagBlocks Y) (anticommPart T (offDiagBlocks Y)) = 0 := by
      unfold anticommPart frobInner
      rw [Matrix.mul_smul, trace_smul, Matrix.mul_sub, trace_sub]
      have h1 : trace ((diagBlocks Y)ᵀ * offDiagBlocks Y) = 0 :=
        frobInner_diagBlocks_offDiagBlocks Y Y
      have h2 : trace ((diagBlocks Y)ᵀ * (T * offDiagBlocks Y * T)) = 0 := by
        have hIsoInner := frobInner_conj_symm_involution (diagBlocks Y) (offDiagBlocks Y) T hT_symm hT_inv
        rw [hT_diag] at hIsoInner
        unfold frobInner at hIsoInner
        rw [Matrix.transpose_neg, Matrix.neg_mul, trace_neg] at hIsoInner
        have h0 := frobInner_diagBlocks_offDiagBlocks Y Y
        unfold frobInner at h0
        linarith
      simp only [smul_eq_mul, h1, h2]
      ring
    have hAdd : anticommPart T Y = anticommPart T (diagBlocks Y) + anticommPart T (offDiagBlocks Y) := by
      conv_lhs => rw [hDecomp]
      unfold anticommPart
      ext i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.mul_add, Matrix.add_mul, smul_eq_mul]
      ring
    rw [hAdd, ← frobInner_comm (anticommPart T (diagBlocks Y) + anticommPart T (offDiagBlocks Y)) (diagBlocks Y),
      frobInner_add_left, hAntiDiag, frobInner_comm (anticommPart T (offDiagBlocks Y)) (diagBlocks Y), hOrthOff]
    unfold frobNormSq
    linarith
  unfold canonicalPiece
  have hSub := frobNormSq_sub_smul ((1 / 2 : ℝ) • anticommPart T Y) (diagBlocks Y) (1 / 4 : ℝ)
  have hSmul : frobNormSq ((1 / 2 : ℝ) • anticommPart T Y) = (1 / 4 : ℝ) * frobNormSq (anticommPart T Y) := by
    unfold frobNormSq frobInner
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul]
    simp only [smul_eq_mul]
    ring
  have hInSmul : frobInner (diagBlocks Y) ((1 / 2 : ℝ) • anticommPart T Y) =
      (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) := by
    unfold frobInner at hInner ⊢
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, hInner]
  linarith [hSub, hSmul, hInSmul]

/-- **Canonical 4-Term Norm Identity (`canonical_four_term_norm_identity`)**:
For any skew-symmetric `Y ∈ 𝕂_6`, the four canonical symmetric left-partners
`U_r = canonicalPiece T_r Y * T_r` (`r = 0, 1, 2, 3`) satisfy:
`∑_{r=0}^3 ‖U_r‖_F² = ∑_{r=0}^3 ‖canonicalPiece T_r Y‖_F² = (1/4) ‖diagBlocks Y‖_F² + (1/2) ‖offDiagBlocks Y‖_F² = (1/2) ‖Y‖_F² - (1/4) ‖diagBlocks Y‖_F²`. -/
theorem canonical_four_term_norm_identity (Y : Mat6) (hY : Yᵀ = -Y) :
    let Y0 := canonicalPiece T0 Y
    let Y1 := canonicalPiece T1 Y
    let Y2 := canonicalPiece T2 Y
    let Y3 := canonicalPiece T3 Y
    frobNormSq (Y0 * T0) + frobNormSq (Y1 * T1) + frobNormSq (Y2 * T2) + frobNormSq (Y3 * T3) =
      frobNormSq Y0 + frobNormSq Y1 + frobNormSq Y2 + frobNormSq Y3 ∧
    frobNormSq Y0 + frobNormSq Y1 + frobNormSq Y2 + frobNormSq Y3 =
      (1 / 4 : ℝ) * frobNormSq (diagBlocks Y) + (1 / 2 : ℝ) * frobNormSq (offDiagBlocks Y) ∧
    frobNormSq Y0 + frobNormSq Y1 + frobNormSq Y2 + frobNormSq Y3 =
      (1 / 2 : ℝ) * frobNormSq Y - (1 / 4 : ℝ) * frobNormSq (diagBlocks Y) := by
  intro Y0 Y1 Y2 Y3
  have hProps := diagBlocks_skew_properties Y hY 0 0 0
  have n0 := frobNormSq_canonicalPiece_eq T0 Y T0_symm T0_inv hProps.2.2.1
  have n1 := frobNormSq_canonicalPiece_eq T1 Y T1_symm T1_inv hProps.2.2.2.1
  have n2 := frobNormSq_canonicalPiece_eq T2 Y T2_symm T2_inv hProps.2.2.2.2.1
  have n3 := frobNormSq_canonicalPiece_eq T3 Y T3_symm T3_inv hProps.2.2.2.2.2
  have hPars := (klein_four_parseval_skew Y hY).2
  have hPyth := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  dsimp [Y0, Y1, Y2, Y3]
  refine ⟨by linarith [n0.1, n1.1, n2.1, n3.1], ?_, ?_⟩
  · linarith [n0.2, n1.2, n2.2, n3.2, hPars, hPyth]
  · linarith [n0.2, n1.2, n2.2, n3.2, hPars]

/-- **Universal 12-Comparator Energy & Lower Bound Theorem (`byers_nash_universal_12_comparator_bound`)**:
For any `A : Mat6` and `K = skewWitness6 a b c`, with `H = symPart A K` and `Y = L_A(K)`:
1. The 8 canonical same-square comparators `{K T_r, K G_r}` (`‖S‖_F² = ‖K‖_F²`) satisfy the
   unconditional lower bound:
   `∑_{r=0}^3 (‖L_A(K T_r)‖_F² + ‖L_A(K G_r)‖_F²) = 16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² + 8 ‖diagBlocks Y‖_F² + 4 ‖offDiagBlocks Y‖_F² ≥ 16 ‖H‖_F² + 4 ‖Y‖_F²`.
2. Consequently, at least one of the 8 same-square symmetric comparators
   `S ∈ {K T_0, ..., K T_3, K G_0, ..., K G_3}` unconditionally satisfies
   `‖L_A(S)‖_F² ≥ 2 ‖H‖_F² + 2 ‖isoBlockTrace H‖_F² + (1/2) ‖Y‖_F² + (1/2) ‖diagBlocks Y‖_F²`. -/
theorem byers_nash_universal_12_comparator_bound (A : Mat6) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
      frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) +
      frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
      frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3)) =
      16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) +
        8 * frobNormSq (diagBlocks Y) + 4 * frobNormSq (offDiagBlocks Y) ∧
    16 * frobNormSq H + 4 * frobNormSq Y ≤
      frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
        frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) +
        frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
        frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3)) ∧
    (2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * T0)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * T1)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * T2)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * T3)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * G0)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * G1)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * G2)) ∨
      2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
        (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y) ≤
        frobNormSq (lyap A (K * G3))) := by
  intro K H Y
  have h8 := eight_involution_byers_nash_identity A a b c
  have hPyth := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  have hIsoNonneg := frobNormSq_nonneg_gen (isoBlockTrace H)
  have hDiagNonneg := frobNormSq_nonneg_gen (diagBlocks Y)
  dsimp [K, H, Y] at h8 hPyth ⊢
  refine ⟨by linarith [h8, hPyth], by linarith [h8, hIsoNonneg, hDiagNonneg], ?_⟩
  set B := 2 * frobNormSq H + 2 * frobNormSq (isoBlockTrace H) +
    (1 / 2 : ℝ) * frobNormSq Y + (1 / 2 : ℝ) * frobNormSq (diagBlocks Y)
  by_cases h0 : B ≤ frobNormSq (lyap A (K * T0))
  · exact Or.inl h0
  by_cases h1 : B ≤ frobNormSq (lyap A (K * T1))
  · exact Or.inr (Or.inl h1)
  by_cases h2 : B ≤ frobNormSq (lyap A (K * T2))
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : B ≤ frobNormSq (lyap A (K * T3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : B ≤ frobNormSq (lyap A (K * G0))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  by_cases h5 : B ≤ frobNormSq (lyap A (K * G1))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  by_cases h6 : B ≤ frobNormSq (lyap A (K * G2))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  right; right; right; right; right; right; right
  dsimp [B, K, H, Y] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith [h8]

/-! ## Section 4: `W_{pq}`-Commuting (`J`) vs. `W_{pq}`-Anticommuting (`{I₂, F, G}`) 12-Comparator Closure -/

/-- Total 9-dimensional `W_{pq}`-anticommuting (`{I₂, F, G}`) off-diagonal energy of `Y`. -/
def offDiagAnticommEnergy (Y : Mat6) : ℝ :=
  frobNormSq (anticommPart W12 (blockPair12 Y)) +
  frobNormSq (anticommPart W13 (blockPair13 Y)) +
  frobNormSq (anticommPart W23 (blockPair23 Y))

/-- Total 3-dimensional `W_{pq}`-commuting (`J`) off-diagonal energy of `Y`. -/
def offDiagCommJEnergy (Y : Mat6) : ℝ :=
  frobNormSq (commPart W12 (blockPair12 Y)) +
  frobNormSq (commPart W13 (blockPair13 Y)) +
  frobNormSq (commPart W23 (blockPair23 Y))

lemma offDiagAnticommEnergy_nonneg (Y : Mat6) : 0 ≤ offDiagAnticommEnergy Y := by
  unfold offDiagAnticommEnergy
  have h1 := frobNormSq_nonneg_gen (anticommPart W12 (blockPair12 Y))
  have h2 := frobNormSq_nonneg_gen (anticommPart W13 (blockPair13 Y))
  have h3 := frobNormSq_nonneg_gen (anticommPart W23 (blockPair23 Y))
  linarith

lemma offDiagCommJEnergy_nonneg (Y : Mat6) : 0 ≤ offDiagCommJEnergy Y := by
  unfold offDiagCommJEnergy
  have h1 := frobNormSq_nonneg_gen (commPart W12 (blockPair12 Y))
  have h2 := frobNormSq_nonneg_gen (commPart W13 (blockPair13 Y))
  have h3 := frobNormSq_nonneg_gen (commPart W23 (blockPair23 Y))
  linarith

/-- Orthogonal energy split of `offDiagBlocks Y` and `Y` into `offDiagAnticommEnergy Y`
(`{I₂, F, G}` components) and `offDiagCommJEnergy Y` (`J` components). -/
theorem frobNormSq_offDiagBlocks_eq_anticomm_add_commJ (Y : Mat6) :
    frobNormSq (offDiagBlocks Y) = offDiagAnticommEnergy Y + offDiagCommJEnergy Y ∧
    frobNormSq Y =
      frobNormSq (diagBlocks Y) + offDiagAnticommEnergy Y + offDiagCommJEnergy Y := by
  have h12 := frobNormSq_eq_anticommPart_add_commPart W12 (blockPair12 Y) W12_symm W12_inv
  have h13 := frobNormSq_eq_anticommPart_add_commPart W13 (blockPair13 Y) W13_symm W13_inv
  have h23 := frobNormSq_eq_anticommPart_add_commPart W23 (blockPair23 Y) W23_symm W23_inv
  have hOff := frobNormSq_offDiagBlocks_eq_sum_blockPairs Y
  have hDiag := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  unfold offDiagAnticommEnergy offDiagCommJEnergy
  constructor <;> linarith

lemma J6_eq_T0_mul_G0 : J6 = T0 * G0 := by
  ext i j
  rw [T0_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [J6, skewWitness6, d0, G0, s0, swapIdx]

private lemma T0_anticomm_commPart_W (Y : Mat6) (hY : Yᵀ = -Y) :
    T0 * commPart W12 (blockPair12 Y) = -commPart W12 (blockPair12 Y) * T0 ∧
    T0 * commPart W13 (blockPair13 Y) = -commPart W13 (blockPair13 Y) * T0 ∧
    T0 * commPart W23 (blockPair23 Y) = -commPart W23 (blockPair23 Y) * T0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have hij := congr_fun (congr_fun hY (perm12 i)) (perm12 j)
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
    rw [T0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T0_apply]
    simp only [commPart, Matrix.smul_apply, Matrix.add_apply, W12_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [d0, perm12, blockPair12, planeOf] at hij ⊢ <;> linarith
  · ext i j
    have hij := congr_fun (congr_fun hY (perm13 i)) (perm13 j)
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
    rw [T0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T0_apply]
    simp only [commPart, Matrix.smul_apply, Matrix.add_apply, W13_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [d0, perm13, blockPair13, planeOf] at hij ⊢ <;> linarith
  · ext i j
    have hij := congr_fun (congr_fun hY (perm23 i)) (perm23 j)
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
    rw [T0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_T0_apply]
    simp only [commPart, Matrix.smul_apply, Matrix.add_apply, W23_conj_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [d0, perm23, blockPair23, planeOf] at hij ⊢ <;> linarith

private lemma G0_anticomm_commPart_W12 (Y : Mat6) (hY : Yᵀ = -Y) :
    G0 * commPart W12 (blockPair12 Y) = -commPart W12 (blockPair12 Y) * G0 := by
  ext i j
  have hij1 := congr_fun (congr_fun hY j) (swapIdx i)
  have hij2 := congr_fun (congr_fun hY (perm12 j)) (perm12 (swapIdx i))
  have hij3 := congr_fun (congr_fun hY (swapIdx j)) i
  have hij4 := congr_fun (congr_fun hY (perm12 (swapIdx j))) (perm12 i)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij1 hij2 hij3 hij4
  rw [G0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G0_apply]
  simp only [commPart, Matrix.smul_apply, Matrix.add_apply, W12_conj_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [s0, swapIdx, perm12, blockPair12, planeOf] at hij1 hij2 hij3 hij4 ⊢ <;> linarith

private lemma G0_anticomm_commPart_W13 (Y : Mat6) (hY : Yᵀ = -Y) :
    G0 * commPart W13 (blockPair13 Y) = -commPart W13 (blockPair13 Y) * G0 := by
  ext i j
  have hij1 := congr_fun (congr_fun hY j) (swapIdx i)
  have hij2 := congr_fun (congr_fun hY (perm13 j)) (perm13 (swapIdx i))
  have hij3 := congr_fun (congr_fun hY (swapIdx j)) i
  have hij4 := congr_fun (congr_fun hY (perm13 (swapIdx j))) (perm13 i)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij1 hij2 hij3 hij4
  rw [G0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G0_apply]
  simp only [commPart, Matrix.smul_apply, Matrix.add_apply, W13_conj_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [s0, swapIdx, perm13, blockPair13, planeOf] at hij1 hij2 hij3 hij4 ⊢ <;> linarith

private lemma G0_anticomm_commPart_W23 (Y : Mat6) (hY : Yᵀ = -Y) :
    G0 * commPart W23 (blockPair23 Y) = -commPart W23 (blockPair23 Y) * G0 := by
  ext i j
  have hij1 := congr_fun (congr_fun hY j) (swapIdx i)
  have hij2 := congr_fun (congr_fun hY (perm23 j)) (perm23 (swapIdx i))
  have hij3 := congr_fun (congr_fun hY (swapIdx j)) i
  have hij4 := congr_fun (congr_fun hY (perm23 (swapIdx j))) (perm23 i)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij1 hij2 hij3 hij4
  rw [G0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G0_apply]
  simp only [commPart, Matrix.smul_apply, Matrix.add_apply, W23_conj_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [s0, swapIdx, perm23, blockPair23, planeOf] at hij1 hij2 hij3 hij4 ⊢ <;> linarith

/-- **Universal Anticommutation of `T0` and `G0` with the `W_{pq}`-Commuting (`J`) Off-Diagonal Subspace**:
For any skew-symmetric `Y ∈ 𝕂_6` (`Yᵀ = -Y`), each `W_{pq}`-commuting off-diagonal component
`commPart W_{pq} (blockPair_{pq} Y)` lies in `𝕊_3 ⊗ J_2` and therefore strictly anticommutes
with both `T0 = I_3 ⊗ F_2` and `G0 = I_3 ⊗ G_2`, while strictly commuting with `J6 = I_3 ⊗ J_2`. -/
theorem T0_G0_anticomm_offDiag_commPart_W (Y : Mat6) (hY : Yᵀ = -Y) :
    T0 * commPart W12 (blockPair12 Y) = -commPart W12 (blockPair12 Y) * T0 ∧
    T0 * commPart W13 (blockPair13 Y) = -commPart W13 (blockPair13 Y) * T0 ∧
    T0 * commPart W23 (blockPair23 Y) = -commPart W23 (blockPair23 Y) * T0 ∧
    G0 * commPart W12 (blockPair12 Y) = -commPart W12 (blockPair12 Y) * G0 ∧
    G0 * commPart W13 (blockPair13 Y) = -commPart W13 (blockPair13 Y) * G0 ∧
    G0 * commPart W23 (blockPair23 Y) = -commPart W23 (blockPair23 Y) * G0 ∧
    J6 * commPart W12 (blockPair12 Y) = commPart W12 (blockPair12 Y) * J6 ∧
    J6 * commPart W13 (blockPair13 Y) = commPart W13 (blockPair13 Y) * J6 ∧
    J6 * commPart W23 (blockPair23 Y) = commPart W23 (blockPair23 Y) * J6 := by
  have hT := T0_anticomm_commPart_W Y hY
  have hG12 := G0_anticomm_commPart_W12 Y hY
  have hG13 := G0_anticomm_commPart_W13 Y hY
  have hG23 := G0_anticomm_commPart_W23 Y hY
  have comm_J6_of_anticomm (M : Mat6) (hTM : T0 * M = -M * T0) (hGM : G0 * M = -M * G0) :
      J6 * M = M * J6 := by
    calc
      J6 * M = T0 * (G0 * M) := by rw [J6_eq_T0_mul_G0, Matrix.mul_assoc]
      _ = T0 * (-M * G0) := by rw [hGM]
      _ = -(T0 * M) * G0 := by noncomm_ring
      _ = -(-M * T0) * G0 := by rw [hTM]
      _ = M * (T0 * G0) := by noncomm_ring
      _ = M * J6 := by rw [← J6_eq_T0_mul_G0]
  exact ⟨hT.1, hT.2.1, hT.2.2, hG12, hG13, hG23,
    comm_J6_of_anticomm _ hT.1 hG12,
    comm_J6_of_anticomm _ hT.2.1 hG13,
    comm_J6_of_anticomm _ hT.2.2 hG23⟩

/-- **12-Comparator Orthogonal Decomposition & Quadratic Comparison Identity for `(J, {I₂, F, G})`
(`twelve_comparator_j_anticomm_split`)**:
For any `A : Mat6`, `K = skewWitness6 a b c`, `H = symPart A K`, `Y = lyap A K`, and
`Y_r = canonicalPiece T_r Y` (`r = 0, 1, 2, 3`), the 12-comparator family `{K T_r, K G_r, Y_r T_r}`
splits `offDiagBlocks Y` orthogonally into `offDiagAnticommEnergy Y` (`{I₂, F, G}` components)
and `offDiagCommJEnergy Y` (`J` components):
1. `∑_{r=0}^3 (‖L_A(K T_r)‖_F² + ‖L_A(K G_r)‖_F²) = 16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² + 8 ‖diagBlocks Y‖_F² + 4 offDiagAnticommEnergy Y + 4 offDiagCommJEnergy Y`.
2. `∑_{r=0}^3 ((‖L_A(K T_r)‖_F² - ‖Y‖_F²) + (‖L_A(K G_r)‖_F² - ‖Y‖_F²)) = 16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² - 4 offDiagAnticommEnergy Y - 4 offDiagCommJEnergy Y`.
3. `∑_{r=0}^3 ‖Y_r T_r‖_F² = (1/4) ‖diagBlocks Y‖_F² + (1/2) offDiagAnticommEnergy Y + (1/2) offDiagCommJEnergy Y`.
4. `∑_{r=0}^3 ⟨Y_r T_r, L_A(K T_r)⟩_F = ‖Y‖_F²`.
5. For every weight `α : ℝ`,
   `2 α ‖Y‖_F² - α² ((1/4) ‖diagBlocks Y‖_F² + (1/2) offDiagAnticommEnergy Y + (1/2) offDiagCommJEnergy Y) ≤ ∑_{r=0}^3 ‖L_A(K T_r)‖_F²`. -/
theorem twelve_comparator_j_anticomm_split (A : Mat6) (a b c α : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    let Y0 := canonicalPiece T0 Y
    let Y1 := canonicalPiece T1 Y
    let Y2 := canonicalPiece T2 Y
    let Y3 := canonicalPiece T3 Y
    frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
      frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) +
      frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
      frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3)) =
      16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) +
        8 * frobNormSq (diagBlocks Y) +
        4 * offDiagAnticommEnergy Y + 4 * offDiagCommJEnergy Y ∧
    (frobNormSq (lyap A (K * T0)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * T1)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * T2)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * T3)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G0)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G1)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G2)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G3)) - frobNormSq Y) =
      16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) -
        4 * offDiagAnticommEnergy Y - 4 * offDiagCommJEnergy Y ∧
    frobNormSq (Y0 * T0) + frobNormSq (Y1 * T1) +
      frobNormSq (Y2 * T2) + frobNormSq (Y3 * T3) =
      (1 / 4 : ℝ) * frobNormSq (diagBlocks Y) +
        (1 / 2 : ℝ) * offDiagAnticommEnergy Y + (1 / 2 : ℝ) * offDiagCommJEnergy Y ∧
    frobInner (Y0 * T0) (lyap A (K * T0)) + frobInner (Y1 * T1) (lyap A (K * T1)) +
      frobInner (Y2 * T2) (lyap A (K * T2)) + frobInner (Y3 * T3) (lyap A (K * T3)) =
      frobNormSq Y ∧
    2 * α * frobNormSq Y -
      α ^ 2 * ((1 / 4 : ℝ) * frobNormSq (diagBlocks Y) +
        (1 / 2 : ℝ) * offDiagAnticommEnergy Y + (1 / 2 : ℝ) * offDiagCommJEnergy Y) ≤
      frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
        frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) := by
  intro K H Y Y0 Y1 Y2 Y3
  have hK := skewWitness6_skew a b c
  have hY := lyap_skew_of_skew A K hK
  have h12 := (byers_nash_universal_12_comparator_bound A a b c).1
  have hSplit := frobNormSq_offDiagBlocks_eq_anticomm_add_commJ Y
  have hCanNorm := canonical_four_term_norm_identity Y hY
  have hCanDecomp := canonical_four_term_decomposition A Y hY a b c
  have hPair :
      frobInner (Y0 * T0) (lyap A (K * T0)) + frobInner (Y1 * T1) (lyap A (K * T1)) +
        frobInner (Y2 * T2) (lyap A (K * T2)) + frobInner (Y3 * T3) (lyap A (K * T3)) =
        frobNormSq Y := by
    have hp := hCanDecomp.2.2.2.2.2.2.2.2.2.2
    dsimp [K, Y, Y0, Y1, Y2, Y3] at hp ⊢
    exact hp
  have hSub0 := frobNormSq_sub_smul (lyap A (K * T0)) (Y0 * T0) α
  have hSub1 := frobNormSq_sub_smul (lyap A (K * T1)) (Y1 * T1) α
  have hSub2 := frobNormSq_sub_smul (lyap A (K * T2)) (Y2 * T2) α
  have hSub3 := frobNormSq_sub_smul (lyap A (K * T3)) (Y3 * T3) α
  have hPos0 := frobNormSq_nonneg_gen (lyap A (K * T0) - α • (Y0 * T0))
  have hPos1 := frobNormSq_nonneg_gen (lyap A (K * T1) - α • (Y1 * T1))
  have hPos2 := frobNormSq_nonneg_gen (lyap A (K * T2) - α • (Y2 * T2))
  have hPos3 := frobNormSq_nonneg_gen (lyap A (K * T3) - α • (Y3 * T3))
  dsimp [K, H, Y, Y0, Y1, Y2, Y3] at h12 hSplit hCanNorm hPair ⊢
  refine ⟨by linarith [h12, hSplit.1], by linarith [h12, hSplit.1, hSplit.2],
    by linarith [hCanNorm.1, hCanNorm.2.1, hSplit.1], hPair, ?_⟩
  have hSumPos :
      0 ≤ (frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
            frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3))) -
          2 * α * (frobInner (Y0 * T0) (lyap A (K * T0)) +
            frobInner (Y1 * T1) (lyap A (K * T1)) +
            frobInner (Y2 * T2) (lyap A (K * T2)) +
            frobInner (Y3 * T3) (lyap A (K * T3))) +
          α ^ 2 * (frobNormSq (Y0 * T0) + frobNormSq (Y1 * T1) +
            frobNormSq (Y2 * T2) + frobNormSq (Y3 * T3)) := by
    linarith [hSub0, hSub1, hSub2, hSub3, hPos0, hPos1, hPos2, hPos3]
  have hUNorm :
      frobNormSq (Y0 * T0) + frobNormSq (Y1 * T1) +
        frobNormSq (Y2 * T2) + frobNormSq (Y3 * T3) =
      (1 / 4 : ℝ) * frobNormSq (diagBlocks Y) +
        (1 / 2 : ℝ) * offDiagAnticommEnergy Y + (1 / 2 : ℝ) * offDiagCommJEnergy Y := by
    linarith [hCanNorm.1, hCanNorm.2.1, hSplit.1]
  rw [hPair, hUNorm] at hSumPos
  linarith

/-- **Explicit Dominance Bounds Under `J`-Commuting Off-Diagonal Energy Bounds
(`twelve_comparator_dominance_of_j_comm_bound`)**:
For any `A : Mat6`, `K = skewWitness6 a b c`, `H = symPart A K`, and `Y = lyap A K`:
1. Combining the 8-comparator Parseval identity with the 4-term canonical quadratic bound at
   `α = 2` yields the unconditional positive-coefficient lower bound:
   `16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² + 4 ‖Y‖_F² + 7 ‖diagBlocks Y‖_F² + 2 offDiagAnticommEnergy Y + 2 offDiagCommJEnergy Y ≤ 2 ∑_{r=0}^3 ‖L_A(K T_r)‖_F² + ∑_{r=0}^3 ‖L_A(K G_r)‖_F²`.
2. Whenever `offDiagCommJEnergy Y ≤ 4 ‖H‖_F² + 4 ‖isoBlockTrace H‖_F² - offDiagAnticommEnergy Y`,
   at least one of the 8 canonical same-square comparators `S ∈ {K T_r, K G_r}` dominates `‖Y‖_F²`.
3. Whenever `offDiagCommJEnergy Y ≤ (7/2) ‖diagBlocks Y‖_F² + offDiagAnticommEnergy Y + 8 ‖H‖_F² + 8 ‖isoBlockTrace H‖_F²`,
   the weighted 12-comparator sum `2 ∑_{r=0}^3 ‖L_A(K T_r)‖_F² + ∑_{r=0}^3 ‖L_A(K G_r)‖_F²`
   dominates `4 ‖Y‖_F² + 4 offDiagCommJEnergy Y`. -/
theorem twelve_comparator_dominance_of_j_comm_bound (A : Mat6) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) +
      4 * frobNormSq Y + 7 * frobNormSq (diagBlocks Y) +
      2 * offDiagAnticommEnergy Y + 2 * offDiagCommJEnergy Y ≤
      2 * (frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
           frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3))) +
      (frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
       frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3))) ∧
    (offDiagCommJEnergy Y ≤
        4 * frobNormSq H + 4 * frobNormSq (isoBlockTrace H) - offDiagAnticommEnergy Y →
      frobNormSq Y ≤ frobNormSq (lyap A (K * T0)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * T1)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * T2)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * T3)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G0)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G1)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G2)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G3))) ∧
    (offDiagCommJEnergy Y ≤
        (7 / 2 : ℝ) * frobNormSq (diagBlocks Y) + offDiagAnticommEnergy Y +
          8 * frobNormSq H + 8 * frobNormSq (isoBlockTrace H) →
      4 * frobNormSq Y + 4 * offDiagCommJEnergy Y ≤
        2 * (frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
             frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3))) +
        (frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
         frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3)))) := by
  intro K H Y
  have hSplit := twelve_comparator_j_anticomm_split A a b c 2
  have hDom := (eight_involution_dominance_of_commutator_or_diag A a b c).2
  have hOff := (frobNormSq_offDiagBlocks_eq_anticomm_add_commJ Y).1
  dsimp [K, H, Y] at hSplit hDom hOff ⊢
  have hComb :
      16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) +
        4 * frobNormSq Y + 7 * frobNormSq (diagBlocks Y) +
        2 * offDiagAnticommEnergy Y + 2 * offDiagCommJEnergy Y ≤
        2 * (frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
             frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3))) +
        (frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
         frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3))) := by
    linarith [hSplit.1, hSplit.2.2.2.2]
  refine ⟨hComb, fun hCond => hDom (by linarith [hOff, hCond]), fun hCond2 => ?_⟩
  linarith [hComb, hCond2]

#print axioms lyap_symm_skew_orthogonal_decomp
#print axioms lyapunov_singular_value_robustness_bound
#print axioms plane_swap_involutions_properties
#print axioms plane_swap_conj_skewWitness6
#print axioms plane_swap_comm_J6
#print axioms equal_freq_f_swap_involutions_anticomm
#print axioms frobNormSq_offDiagBlocks_eq_sum_blockPairs
#print axioms skew6_fifteen_dim_parseval
#print axioms canonical_four_term_norm_identity
#print axioms byers_nash_universal_12_comparator_bound
#print axioms frobNormSq_offDiagBlocks_eq_anticomm_add_commJ
#print axioms T0_G0_anticomm_offDiag_commPart_W
#print axioms twelve_comparator_j_anticomm_split
#print axioms twelve_comparator_dominance_of_j_comm_bound

end
end Research.ByersNashOffDiagComplete
