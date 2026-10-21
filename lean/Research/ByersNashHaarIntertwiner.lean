import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Research.ByersNashMultiTerm

/-!
# Symmetric Intertwiner Duality & 8-Involution (F, G)-Klein Haar Parseval Theorem

This module extends `Research.ByersNashMultiTerm` for the full-rank `6 × 6` Byers–Nash
conjecture (Lane MF-13) with three main results:

1. **Symmetric Intertwiner Duality (`symmetric_intertwiner_lyap_pairing`,
   `symmetric_intertwiner_self_bound`)**:
   For arbitrary dimension `n`, if `K, Y ∈ 𝕂_n` are skew-symmetric and `S ∈ 𝕊_n` is a
   symmetric involution (`Sᵀ = S`, `S * S = 1`) satisfying the linear intertwiner equation
   `S * K = Y * S`, then `U_S := -Y * S * Y = -Y * K * S` is also symmetric (`U_Sᵀ = U_S`),
   satisfies `U_S * S = -(Y * K)`, and for **every** `A : Matrix n n ℝ`:
   `⟨-Y * S * Y, L_A(S)⟩_F = ⟨Y, L_A(K)⟩_F`.
   When `Y = L_A(K)`, this yields `⟨-Y * S * Y, L_A(S)⟩_F = ‖L_A(K)‖_F²` identically.

2. **Canonical 4-Term Symmetric Decomposition (`canonical_four_term_decomposition`)**:
   For any skew-symmetric `Y ∈ 𝕂_6` and `K = skewWitness6 a b c`, the four pieces
   `Y_r := (1/2) • anticommPart T_r Y - (1/4) • diagBlocks Y` (`r = 0, 1, 2, 3`)
   are skew-symmetric, strictly anticommute with `T_r`, sum to `Y`, and produce symmetric
   pairs `(Y_r * T_r, K * T_r)` satisfying `∑_r (Y_r * T_r) * (K * T_r) = -(Y * K)` and
   `∑_r ⟨Y_r * T_r, L_A(K * T_r)⟩_F = ⟨Y, L_A(K)⟩_F`.

3. **8-Involution `(F, G)`-Klein Haar Projection & Parseval Theorem
   (`eight_involution_haar_projection`, `eight_involution_parseval_identity`,
   `eight_involution_byers_nash_identity`,
   `eight_involution_dominance_of_commutator_or_diag`)**:
   Combining the four `F`-type Klein involutions `{T_0, T_1, T_2, T_3}` with the four
   `G`-type Klein involutions `{G_0, G_1, G_2, G_3}` (`G = [[0, 1], [1, 0]]`) yields an
   8-element family of symmetric involutions anticommuting with `skewWitness6 a b c`.
   Averaging `T * H * T` over all 8 involutions for any `H ∈ 𝕊_6` equals the exact
   continuous 3-torus Haar projection onto the isotropic block-trace subspace:
   `isoBlockTrace H = diag(((H₀₀+H₁₁)/2) I₂, ((H₂₂+H₃₃)/2) I₂, ((H₄₄+H₅₅)/2) I₂)`.
   Consequently,
   `∑_{r=0}^3 (‖L_A(K T_r)‖_F² + ‖L_A(K G_r)‖_F²) = 16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² + 4 ‖Y‖_F² + 4 ‖diagBlocks Y‖_F²`.
   In particular, whenever `4 ‖H‖_F² + 4 ‖isoBlockTrace H‖_F² ≥ ‖offDiagBlocks Y‖_F²`,
   at least one of the 8 canonical same-square symmetric comparators `{K T_r, K G_r}`
   dominates `‖L_A(K)‖_F²`.
-/

namespace Research.ByersNashHaarIntertwiner

open Matrix BigOperators
open Research.ByersNashDuality
open Research.ByersNashMultiTerm

noncomputable section

/-! ## Section 1: Symmetric Intertwiner Duality in Arbitrary Dimension `n` -/

variable {n : Type*} [Fintype n]

/-- If `K, Y` are skew-symmetric and `S` is symmetric with `S * K = Y * S`, then
taking transposes yields `K * S = S * Y`. -/
lemma symmetric_intertwiner_transpose_comm
    (K Y S : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hY : Yᵀ = -Y) (hS : Sᵀ = S)
    (hInter : S * K = Y * S) :
    K * S = S * Y := by
  have hT := congrArg Matrix.transpose hInter
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hK, hY, hS,
    Matrix.neg_mul, Matrix.mul_neg, neg_inj] at hT
  exact hT

/-- For any skew-symmetric `Y` and symmetric `S`, the matrix `U_S = -Y * S * Y` is symmetric. -/
lemma neg_mul_symm_mul_skew_symm (Y S : Matrix n n ℝ) (hY : Yᵀ = -Y) (hS : Sᵀ = S) :
    (-Y * S * Y)ᵀ = -Y * S * Y := by
  calc
    (-Y * S * Y)ᵀ = Yᵀ * Sᵀ * (-Y)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (-Y) * S * Y := by
      rw [hY, hS, Matrix.transpose_neg, hY, neg_neg]
    _ = -Y * S * Y := by noncomm_ring

/-- **Symmetric Intertwiner Lyapunov Pairing Theorem**:
For any `A, K, Y, S : Matrix n n ℝ` with `Kᵀ = -K`, `Yᵀ = -Y`, `Sᵀ = S`, `S * S = 1`,
and `S * K = Y * S`, both `U_S = -Y * S * Y` and `S` are symmetric, their product is
`U_S * S = -(Y * K)`, and for **every** `A : Matrix n n ℝ`:
`⟨-Y * S * Y, L_A(S)⟩_F = ⟨Y, L_A(K)⟩_F`. -/
theorem symmetric_intertwiner_lyap_pairing [DecidableEq n]
    (A K Y S : Matrix n n ℝ)
    (hK : Kᵀ = -K) (hY : Yᵀ = -Y) (hS : Sᵀ = S) (hS2 : S * S = 1)
    (hInter : S * K = Y * S) :
    let U_S := -Y * S * Y
    U_Sᵀ = U_S ∧
    U_S * S = -(Y * K) ∧
    frobInner U_S (lyap A S) = frobInner Y (lyap A K) := by
  intro U_S
  have hKS : K * S = S * Y := symmetric_intertwiner_transpose_comm K Y S hK hY hS hInter
  have hUS_symm : U_Sᵀ = U_S := neg_mul_symm_mul_skew_symm Y S hY hS
  have hUS_mul : U_S * S = -(Y * K) := by
    dsimp [U_S]
    calc
      (-Y * S * Y) * S = -Y * (S * Y) * S := by noncomm_ring
      _ = -Y * (K * S) * S := by rw [← hKS]
      _ = -(Y * K) * (S * S) := by noncomm_ring
      _ = -(Y * K) * 1 := by rw [hS2]
      _ = -(Y * K) := by rw [Matrix.mul_one]
  refine ⟨hUS_symm, hUS_mul, ?_⟩
  rw [lyap_frobInner_symm A U_S S hUS_symm hS,
      lyap_frobInner_skew A Y K hY hK, hUS_mul]
  unfold frobInner
  rw [Matrix.mul_neg, trace_neg]
  ring

/-- Expansion of `‖X - α • U‖_F²` in arbitrary dimension `n`. -/
lemma frobNormSq_sub_smul (X U : Matrix n n ℝ) (α : ℝ) :
    frobNormSq (X - α • U) = frobNormSq X - 2 * α * frobInner U X + α ^ 2 * frobNormSq U := by
  have hComm : frobInner X U = frobInner U X := frobInner_comm X U
  unfold frobNormSq frobInner at hComm ⊢
  rw [Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    trace_sub, trace_sub, trace_sub, trace_smul, trace_smul, trace_smul, trace_smul]
  simp only [smul_eq_mul]
  rw [hComm]
  ring

/-- Nonnegativity of `frobNormSq M` in arbitrary dimension `n`. -/
lemma frobNormSq_nonneg_gen (M : Matrix n n ℝ) : 0 ≤ frobNormSq M := by
  unfold frobNormSq frobInner Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (M j i)

/-- **Symmetric Intertwiner Self-Bound Theorem**:
Under the hypotheses of `symmetric_intertwiner_lyap_pairing`, for every `A : Matrix n n ℝ`
with `Y = L_A(K)` and every weight `α : ℝ`,
`2 * α * ‖L_A(K)‖_F² - α² * ‖Y * S * Y‖_F² ≤ ‖L_A(S)‖_F²`. -/
theorem symmetric_intertwiner_self_bound [DecidableEq n]
    (A K S : Matrix n n ℝ) (α : ℝ)
    (hK : Kᵀ = -K) (hS : Sᵀ = S) (hS2 : S * S = 1)
    (hInter : S * K = lyap A K * S) :
    let Y := lyap A K
    2 * α * frobNormSq Y - α ^ 2 * frobNormSq (Y * S * Y) ≤ frobNormSq (lyap A S) := by
  intro Y
  have hY : Yᵀ = -Y := lyap_skew_of_skew A K hK
  have hPair : frobInner (-Y * S * Y) (lyap A S) = frobNormSq Y :=
    (symmetric_intertwiner_lyap_pairing A K Y S hK hY hS hS2 hInter).2.2
  have hNonneg := frobNormSq_nonneg_gen (lyap A S - α • (-Y * S * Y))
  have hExpand := frobNormSq_sub_smul (lyap A S) (-Y * S * Y) α
  have hUNorm : frobNormSq (-Y * S * Y) = frobNormSq (Y * S * Y) := by
    have hNeg : -Y * S * Y = -(Y * S * Y) := by noncomm_ring
    rw [hNeg, frobNormSq_neg]
  rw [hPair, hUNorm] at hExpand
  linarith

/-! ## Section 2: Canonical 4-Term Symmetric Decomposition on `6 × 6` Matrices -/

/-- Canonical `r`-th piece of a skew-symmetric `6 × 6` matrix `Y` with respect to an
involution `T`: `canonicalPiece T Y = (1/2) • anticommPart T Y - (1/4) • diagBlocks Y`. -/
def canonicalPiece (T Y : Mat6) : Mat6 :=
  (1 / 2 : ℝ) • anticommPart T Y - (1 / 4 : ℝ) • diagBlocks Y

lemma canonicalPiece_skew (T Y : Mat6) (hT : Tᵀ = T) (hY : Yᵀ = -Y) :
    (canonicalPiece T Y)ᵀ = -canonicalPiece T Y := by
  unfold canonicalPiece
  have hAnti := anticommPart_skew T Y hT hY
  have hDiag := (diagBlocks_skew_properties Y hY 0 0 0).1
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, hAnti, hDiag]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- The four canonical pieces `canonicalPiece T_r Y` (`r = 0, 1, 2, 3`) are skew-symmetric,
strictly anticommute with `T_r`, sum to `Y`, and yield symmetric pairs `(U_r, V_r) = (Y_r T_r, K T_r)`
satisfying `∑_r U_r * V_r = -(Y * K)` and `∑_r ⟨U_r, L_A(V_r)⟩_F = ⟨Y, L_A(K)⟩_F`. -/
theorem canonical_four_term_decomposition
    (A : Mat6) (Y : Mat6) (hY : Yᵀ = -Y) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let Y0 := canonicalPiece T0 Y
    let Y1 := canonicalPiece T1 Y
    let Y2 := canonicalPiece T2 Y
    let Y3 := canonicalPiece T3 Y
    Y0ᵀ = -Y0 ∧ Y1ᵀ = -Y1 ∧ Y2ᵀ = -Y2 ∧ Y3ᵀ = -Y3 ∧
    T0 * Y0 = -Y0 * T0 ∧ T1 * Y1 = -Y1 * T1 ∧ T2 * Y2 = -Y2 * T2 ∧ T3 * Y3 = -Y3 * T3 ∧
    Y0 + Y1 + Y2 + Y3 = Y ∧
    (Y0 * T0) * (K * T0) + (Y1 * T1) * (K * T1) + (Y2 * T2) * (K * T2) + (Y3 * T3) * (K * T3) = -(Y * K) ∧
    frobInner (Y0 * T0) (lyap A (K * T0)) + frobInner (Y1 * T1) (lyap A (K * T1)) +
      frobInner (Y2 * T2) (lyap A (K * T2)) + frobInner (Y3 * T3) (lyap A (K * T3)) =
      frobInner Y (lyap A K) := by
  intro K Y0 Y1 Y2 Y3
  have hK := skewWitness6_skew a b c
  have hProps := diagBlocks_skew_properties Y hY a b c
  have hY0_skew : Y0ᵀ = -Y0 := canonicalPiece_skew T0 Y T0_symm hY
  have hY1_skew : Y1ᵀ = -Y1 := canonicalPiece_skew T1 Y T1_symm hY
  have hY2_skew : Y2ᵀ = -Y2 := canonicalPiece_skew T2 Y T2_symm hY
  have hY3_skew : Y3ᵀ = -Y3 := canonicalPiece_skew T3 Y T3_symm hY
  have hY0_anti : T0 * Y0 = -Y0 * T0 := by
    dsimp [Y0, canonicalPiece]
    have h1 := mul_anticommPart_involution T0 Y T0_inv
    have h2 := hProps.2.2.1
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h1, h2]
    ext i j; simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.neg_mul, Matrix.sub_mul, Matrix.smul_mul, smul_eq_mul]; ring
  have hY1_anti : T1 * Y1 = -Y1 * T1 := by
    dsimp [Y1, canonicalPiece]
    have h1 := mul_anticommPart_involution T1 Y T1_inv
    have h2 := hProps.2.2.2.1
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h1, h2]
    ext i j; simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.neg_mul, Matrix.sub_mul, Matrix.smul_mul, smul_eq_mul]; ring
  have hY2_anti : T2 * Y2 = -Y2 * T2 := by
    dsimp [Y2, canonicalPiece]
    have h1 := mul_anticommPart_involution T2 Y T2_inv
    have h2 := hProps.2.2.2.2.1
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h1, h2]
    ext i j; simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.neg_mul, Matrix.sub_mul, Matrix.smul_mul, smul_eq_mul]; ring
  have hY3_anti : T3 * Y3 = -Y3 * T3 := by
    dsimp [Y3, canonicalPiece]
    have h1 := mul_anticommPart_involution T3 Y T3_inv
    have h2 := hProps.2.2.2.2.2
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h1, h2]
    ext i j; simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.neg_mul, Matrix.sub_mul, Matrix.smul_mul, smul_eq_mul]; ring
  have hSum : Y0 + Y1 + Y2 + Y3 = Y := by
    have hAvg := klein_four_average_skew Y hY
    ext i j
    have hij := congr_fun (congr_fun hAvg i) j
    change ((1 / 2 : ℝ) • anticommPart T0 Y - (1 / 4 : ℝ) • diagBlocks Y +
            ((1 / 2 : ℝ) • anticommPart T1 Y - (1 / 4 : ℝ) • diagBlocks Y) +
            ((1 / 2 : ℝ) • anticommPart T2 Y - (1 / 4 : ℝ) • diagBlocks Y) +
            ((1 / 2 : ℝ) • anticommPart T3 Y - (1 / 4 : ℝ) • diagBlocks Y)) i j = Y i j
    unfold anticommPart
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul] at hij ⊢
    linarith
  have hProd :
      (Y0 * T0) * (K * T0) + (Y1 * T1) * (K * T1) + (Y2 * T2) * (K * T2) + (Y3 * T3) * (K * T3) =
        -(Y * K) := by
    rw [common_involution_product_eq Y0 K T0 T0_inv (T0_anticomm_skewWitness6 a b c),
        common_involution_product_eq Y1 K T1 T1_inv (T1_anticomm_skewWitness6 a b c),
        common_involution_product_eq Y2 K T2 T2_inv (T2_anticomm_skewWitness6 a b c),
        common_involution_product_eq Y3 K T3 T3_inv (T3_anticomm_skewWitness6 a b c)]
    calc
      -(Y0 * K) + -(Y1 * K) + -(Y2 * K) + -(Y3 * K) = -((Y0 + Y1 + Y2 + Y3) * K) := by noncomm_ring
      _ = -(Y * K) := by rw [hSum]
  have hPair :
      frobInner (Y0 * T0) (lyap A (K * T0)) + frobInner (Y1 * T1) (lyap A (K * T1)) +
        frobInner (Y2 * T2) (lyap A (K * T2)) + frobInner (Y3 * T3) (lyap A (K * T3)) =
        frobInner Y (lyap A K) := by
    rw [common_involution_lyap_pairing A Y0 K T0 hY0_skew hK T0_symm T0_inv hY0_anti (T0_anticomm_skewWitness6 a b c),
        common_involution_lyap_pairing A Y1 K T1 hY1_skew hK T1_symm T1_inv hY1_anti (T1_anticomm_skewWitness6 a b c),
        common_involution_lyap_pairing A Y2 K T2 hY2_skew hK T2_symm T2_inv hY2_anti (T2_anticomm_skewWitness6 a b c),
        common_involution_lyap_pairing A Y3 K T3 hY3_skew hK T3_symm T3_inv hY3_anti (T3_anticomm_skewWitness6 a b c),
        ← frobInner_add_left, ← frobInner_add_left, ← frobInner_add_left, hSum]
  exact ⟨hY0_skew, hY1_skew, hY2_skew, hY3_skew,
    hY0_anti, hY1_anti, hY2_anti, hY3_anti, hSum, hProd, hPair⟩

/-! ## Section 3: The Four `G`-Type Klein Involutions `G0, G1, G2, G3` -/

/-- Intra-plane swap involution on `Fin 6`: `0 ↔ 1`, `2 ↔ 3`, `4 ↔ 5`. -/
def swapIdx : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

lemma swapIdx_involutive (i : Fin 6) : swapIdx (swapIdx i) = i := by
  fin_cases i <;> rfl

/-- Plane-constant sign vectors `s0, s1, s2, s3 : Fin 6 → ℝ` for the four Klein characters. -/
def s0 : Fin 6 → ℝ := ![1, 1, 1, 1, 1, 1]
def s1 : Fin 6 → ℝ := ![1, 1, -1, -1, -1, -1]
def s2 : Fin 6 → ℝ := ![-1, -1, 1, 1, -1, -1]
def s3 : Fin 6 → ℝ := ![-1, -1, -1, -1, 1, 1]

/-- The four `G`-type Klein involutions `G_r = diag(ε_{r,1} G, ε_{r,2} G, ε_{r,3} G)`
with `G = [[0, 1], [1, 0]]`. -/
def G0 : Mat6 := Matrix.of fun i j => if j = swapIdx i then s0 i else 0
def G1 : Mat6 := Matrix.of fun i j => if j = swapIdx i then s1 i else 0
def G2 : Mat6 := Matrix.of fun i j => if j = swapIdx i then s2 i else 0
def G3 : Mat6 := Matrix.of fun i j => if j = swapIdx i then s3 i else 0

lemma G0_mul_apply (X : Mat6) (i j : Fin 6) : (G0 * X) i j = s0 i * X (swapIdx i) j := by
  fin_cases i <;> simp [G0, s0, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_G0_apply (X : Mat6) (i j : Fin 6) : (X * G0) i j = X i (swapIdx j) * s0 j := by
  fin_cases j <;> simp [G0, s0, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma G0_conj_apply (X : Mat6) (i j : Fin 6) :
    (G0 * X * G0) i j = s0 i * X (swapIdx i) (swapIdx j) * s0 j := by
  rw [mul_G0_apply, G0_mul_apply]

lemma G1_mul_apply (X : Mat6) (i j : Fin 6) : (G1 * X) i j = s1 i * X (swapIdx i) j := by
  fin_cases i <;> simp [G1, s1, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_G1_apply (X : Mat6) (i j : Fin 6) : (X * G1) i j = X i (swapIdx j) * s1 j := by
  fin_cases j <;> simp [G1, s1, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma G1_conj_apply (X : Mat6) (i j : Fin 6) :
    (G1 * X * G1) i j = s1 i * X (swapIdx i) (swapIdx j) * s1 j := by
  rw [mul_G1_apply, G1_mul_apply]

lemma G2_mul_apply (X : Mat6) (i j : Fin 6) : (G2 * X) i j = s2 i * X (swapIdx i) j := by
  fin_cases i <;> simp [G2, s2, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_G2_apply (X : Mat6) (i j : Fin 6) : (X * G2) i j = X i (swapIdx j) * s2 j := by
  fin_cases j <;> simp [G2, s2, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma G2_conj_apply (X : Mat6) (i j : Fin 6) :
    (G2 * X * G2) i j = s2 i * X (swapIdx i) (swapIdx j) * s2 j := by
  rw [mul_G2_apply, G2_mul_apply]

lemma G3_mul_apply (X : Mat6) (i j : Fin 6) : (G3 * X) i j = s3 i * X (swapIdx i) j := by
  fin_cases i <;> simp [G3, s3, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma mul_G3_apply (X : Mat6) (i j : Fin 6) : (X * G3) i j = X i (swapIdx j) * s3 j := by
  fin_cases j <;> simp [G3, s3, swapIdx, Matrix.mul_apply, Fin.sum_univ_succ]

lemma G3_conj_apply (X : Mat6) (i j : Fin 6) :
    (G3 * X * G3) i j = s3 i * X (swapIdx i) (swapIdx j) * s3 j := by
  rw [mul_G3_apply, G3_mul_apply]

lemma G0_symm : G0ᵀ = G0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma G1_symm : G1ᵀ = G1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma G2_symm : G2ᵀ = G2 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma G3_symm : G3ᵀ = G3 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma G0_inv : G0 * G0 = 1 := by
  ext i j; rw [G0_mul_apply]; fin_cases i <;> fin_cases j <;> simp [G0, s0, swapIdx]

lemma G1_inv : G1 * G1 = 1 := by
  ext i j; rw [G1_mul_apply]; fin_cases i <;> fin_cases j <;> simp [G1, s1, swapIdx]

lemma G2_inv : G2 * G2 = 1 := by
  ext i j; rw [G2_mul_apply]; fin_cases i <;> fin_cases j <;> simp [G2, s2, swapIdx]

lemma G3_inv : G3 * G3 = 1 := by
  ext i j; rw [G3_mul_apply]; fin_cases i <;> fin_cases j <;> simp [G3, s3, swapIdx]

lemma G0_anticomm_skewWitness6 (a b c : ℝ) :
    G0 * skewWitness6 a b c = -skewWitness6 a b c * G0 := by
  ext i j
  rw [G0_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G0_apply]
  fin_cases i <;> fin_cases j <;> simp [s0, swapIdx, skewWitness6]

lemma G1_anticomm_skewWitness6 (a b c : ℝ) :
    G1 * skewWitness6 a b c = -skewWitness6 a b c * G1 := by
  ext i j
  rw [G1_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G1_apply]
  fin_cases i <;> fin_cases j <;> simp [s1, swapIdx, skewWitness6]

lemma G2_anticomm_skewWitness6 (a b c : ℝ) :
    G2 * skewWitness6 a b c = -skewWitness6 a b c * G2 := by
  ext i j
  rw [G2_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G2_apply]
  fin_cases i <;> fin_cases j <;> simp [s2, swapIdx, skewWitness6]

lemma G3_anticomm_skewWitness6 (a b c : ℝ) :
    G3 * skewWitness6 a b c = -skewWitness6 a b c * G3 := by
  ext i j
  rw [G3_mul_apply, Matrix.neg_mul, Matrix.neg_apply, mul_G3_apply]
  fin_cases i <;> fin_cases j <;> simp [s3, swapIdx, skewWitness6]

/-- All four `G`-type involutions `G0, G1, G2, G3` are symmetric involutions, anticommute
with `K = skewWitness6 a b c`, and produce symmetric comparators `K * G_r` sharing the
exact square `-K²` and Frobenius norm `‖K‖_F²`. -/
theorem four_G_involutions_same_square (a b c : ℝ) :
    let K := skewWitness6 a b c
    G0ᵀ = G0 ∧ G1ᵀ = G1 ∧ G2ᵀ = G2 ∧ G3ᵀ = G3 ∧
    G0 * G0 = 1 ∧ G1 * G1 = 1 ∧ G2 * G2 = 1 ∧ G3 * G3 = 1 ∧
    G0 * K = -K * G0 ∧ G1 * K = -K * G1 ∧ G2 * K = -K * G2 ∧ G3 * K = -K * G3 ∧
    (K * G0)ᵀ = K * G0 ∧ (K * G1)ᵀ = K * G1 ∧ (K * G2)ᵀ = K * G2 ∧ (K * G3)ᵀ = K * G3 ∧
    (K * G0) * (K * G0) = -(K * K) ∧ (K * G1) * (K * G1) = -(K * K) ∧
    (K * G2) * (K * G2) = -(K * K) ∧ (K * G3) * (K * G3) = -(K * K) ∧
    frobNormSq (K * G0) = frobNormSq K ∧ frobNormSq (K * G1) = frobNormSq K ∧
    frobNormSq (K * G2) = frobNormSq K ∧ frobNormSq (K * G3) = frobNormSq K := by
  intro K
  have hK := skewWitness6_skew a b c
  have hA0 := G0_anticomm_skewWitness6 a b c
  have hA1 := G1_anticomm_skewWitness6 a b c
  have hA2 := G2_anticomm_skewWitness6 a b c
  have hA3 := G3_anticomm_skewWitness6 a b c
  have sq_lem (G : Mat6) (hG_inv : G * G = 1) (hG_anti : G * K = -K * G) :
      (K * G) * (K * G) = -(K * K) := by
    calc
      (K * G) * (K * G) = K * (G * K) * G := by noncomm_ring
      _ = K * (-K * G) * G := by rw [hG_anti]
      _ = -(K * K) * (G * G) := by noncomm_ring
      _ = -(K * K) * 1 := by rw [hG_inv]
      _ = -(K * K) := by rw [Matrix.mul_one]
  refine ⟨G0_symm, G1_symm, G2_symm, G3_symm,
    G0_inv, G1_inv, G2_inv, G3_inv,
    hA0, hA1, hA2, hA3,
    symm_of_skew_mul_anticomm K G0 hK G0_symm hA0,
    symm_of_skew_mul_anticomm K G1 hK G1_symm hA1,
    symm_of_skew_mul_anticomm K G2 hK G2_symm hA2,
    symm_of_skew_mul_anticomm K G3 hK G3_symm hA3,
    sq_lem G0 G0_inv hA0, sq_lem G1 G1_inv hA1,
    sq_lem G2 G2_inv hA2, sq_lem G3 G3_inv hA3,
    frobNormSq_mul_symm_involution K G0 G0_symm G0_inv,
    frobNormSq_mul_symm_involution K G1 G1_symm G1_inv,
    frobNormSq_mul_symm_involution K G2 G2_symm G2_inv,
    frobNormSq_mul_symm_involution K G3 G3_symm G3_inv⟩

/-! ## Section 4: Isotropic Block-Trace Projection & 8-Involution Haar Parseval Theorem -/

/-- Diagonal entries of the isotropic block-trace projection of `H`. -/
def isoDiag (H : Mat6) : Fin 6 → ℝ :=
  ![(1 / 2 : ℝ) * (H 0 0 + H 1 1), (1 / 2 : ℝ) * (H 0 0 + H 1 1),
    (1 / 2 : ℝ) * (H 2 2 + H 3 3), (1 / 2 : ℝ) * (H 2 2 + H 3 3),
    (1 / 2 : ℝ) * (H 4 4 + H 5 5), (1 / 2 : ℝ) * (H 4 4 + H 5 5)]

/-- Isotropic block-trace projection of a `6 × 6` matrix `H`:
`isoBlockTrace H = diag(((H₀₀ + H₁₁)/2) I₂, ((H₂₂ + H₃₃)/2) I₂, ((H₄₄ + H₅₅)/2) I₂)`. -/
def isoBlockTrace (H : Mat6) : Mat6 :=
  Matrix.of fun i j => if i = j then isoDiag H i else 0

/-- **8-Involution `(F, G)`-Klein Haar Projection Theorem**:
For any symmetric `6 × 6` matrix `H` (`Hᵀ = H`), averaging `T * H * T` over the 8 involutions
`{T_0, T_1, T_2, T_3, G_0, G_1, G_2, G_3}` equals `isoBlockTrace H`. -/
theorem eight_involution_haar_projection (H : Mat6) (hH : Hᵀ = H) :
    (1 / 8 : ℝ) •
      (T0 * H * T0 + T1 * H * T1 + T2 * H * T2 + T3 * H * T3 +
       G0 * H * G0 + G1 * H * G1 + G2 * H * G2 + G3 * H * G3) =
      isoBlockTrace H := by
  have h10 : H 1 0 = H 0 1 := by have := congr_fun (congr_fun hH 0) 1; simpa [Matrix.transpose_apply] using this
  have h32 : H 3 2 = H 2 3 := by have := congr_fun (congr_fun hH 2) 3; simpa [Matrix.transpose_apply] using this
  have h54 : H 5 4 = H 4 5 := by have := congr_fun (congr_fun hH 4) 5; simpa [Matrix.transpose_apply] using this
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    T0_conj_apply, T1_conj_apply, T2_conj_apply, T3_conj_apply,
    G0_conj_apply, G1_conj_apply, G2_conj_apply, G3_conj_apply, isoBlockTrace, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp [d0, d1, d2, d3, s0, s1, s2, s3, swapIdx, isoDiag, h10, h32, h54] <;> ring

/-- Averaging `G_r * Y * G_r` over `r ∈ {0, 1, 2, 3}` for skew-symmetric `Y` gives `-diagBlocks Y`. -/
theorem klein_four_G_average_skew (Y : Mat6) (hY : Yᵀ = -Y) :
    (1 / 4 : ℝ) • (G0 * Y * G0 + G1 * Y * G1 + G2 * Y * G2 + G3 * Y * G3) =
      -diagBlocks Y := by
  have h00 : Y 0 0 = 0 := by have := congr_fun (congr_fun hY 0) 0; simp [Matrix.transpose_apply] at this; linarith
  have h11 : Y 1 1 = 0 := by have := congr_fun (congr_fun hY 1) 1; simp [Matrix.transpose_apply] at this; linarith
  have h22 : Y 2 2 = 0 := by have := congr_fun (congr_fun hY 2) 2; simp [Matrix.transpose_apply] at this; linarith
  have h33 : Y 3 3 = 0 := by have := congr_fun (congr_fun hY 3) 3; simp [Matrix.transpose_apply] at this; linarith
  have h44 : Y 4 4 = 0 := by have := congr_fun (congr_fun hY 4) 4; simp [Matrix.transpose_apply] at this; linarith
  have h55 : Y 5 5 = 0 := by have := congr_fun (congr_fun hY 5) 5; simp [Matrix.transpose_apply] at this; linarith
  ext i j
  have hij := congr_fun (congr_fun hY j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul,
    G0_conj_apply, G1_conj_apply, G2_conj_apply, G3_conj_apply]
  fin_cases i <;> fin_cases j <;>
    simp [s0, s1, s2, s3, swapIdx, diagBlocks, planeOf, h00, h11, h22, h33, h44, h55] at hij ⊢ <;> linarith

/-- **Klein 4-Group Parseval Identity for the `G`-Involutions on Skew-Symmetric Matrices**:
For any skew-symmetric `Y ∈ 𝕂_6`:
1. `∑_{r=0}^3 ‖commPart G_r Y‖_F² = 2 ‖offDiagBlocks Y‖_F²`.
2. `∑_{r=0}^3 ‖anticommPart G_r Y‖_F² = 2 ‖Y‖_F² + 2 ‖diagBlocks Y‖_F²`. -/
theorem klein_four_G_parseval_skew (Y : Mat6) (hY : Yᵀ = -Y) :
    frobNormSq (commPart G0 Y) + frobNormSq (commPart G1 Y) +
      frobNormSq (commPart G2 Y) + frobNormSq (commPart G3 Y) =
      2 * frobNormSq (offDiagBlocks Y) ∧
    frobNormSq (anticommPart G0 Y) + frobNormSq (anticommPart G1 Y) +
      frobNormSq (anticommPart G2 Y) + frobNormSq (anticommPart G3 Y) =
      2 * frobNormSq Y + 2 * frobNormSq (diagBlocks Y) := by
  have h0 := frobNormSq_commPart_anticommPart_eq G0 Y G0_symm G0_inv
  have h1 := frobNormSq_commPart_anticommPart_eq G1 Y G1_symm G1_inv
  have h2 := frobNormSq_commPart_anticommPart_eq G2 Y G2_symm G2_inv
  have h3 := frobNormSq_commPart_anticommPart_eq G3 Y G3_symm G3_inv
  have h_avg := klein_four_G_average_skew Y hY
  have h_sum_inner :
      frobInner Y (G0 * Y * G0) + frobInner Y (G1 * Y * G1) +
        frobInner Y (G2 * Y * G2) + frobInner Y (G3 * Y * G3) =
      -4 * frobNormSq (diagBlocks Y) := by
    have h_lin :
        frobInner Y (G0 * Y * G0) + frobInner Y (G1 * Y * G1) +
          frobInner Y (G2 * Y * G2) + frobInner Y (G3 * Y * G3) =
        4 * frobInner Y ((1 / 4 : ℝ) • (G0 * Y * G0 + G1 * Y * G1 + G2 * Y * G2 + G3 * Y * G3)) := by
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

/-- Inner product of any matrix `H` with `isoBlockTrace H` equals `‖isoBlockTrace H‖_F²`. -/
lemma frobInner_isoBlockTrace_self (H : Mat6) :
    frobInner H (isoBlockTrace H) = frobNormSq (isoBlockTrace H) := by
  unfold frobNormSq frobInner isoBlockTrace
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [Fin.sum_univ_six, isoDiag]
  ring

/-- **8-Involution `(F, G)`-Klein Parseval Identity on Symmetric Matrices**:
For any symmetric `H ∈ 𝕊_6` (`Hᵀ = H`):
`∑_{r=0}^3 ‖commPart T_r H‖_F² + ∑_{r=0}^3 ‖commPart G_r H‖_F² = 4 ‖H‖_F² + 4 ‖isoBlockTrace H‖_F²`. -/
theorem eight_involution_parseval_identity (H : Mat6) (hH : Hᵀ = H) :
    frobNormSq (commPart T0 H) + frobNormSq (commPart T1 H) +
      frobNormSq (commPart T2 H) + frobNormSq (commPart T3 H) +
      frobNormSq (commPart G0 H) + frobNormSq (commPart G1 H) +
      frobNormSq (commPart G2 H) + frobNormSq (commPart G3 H) =
      4 * frobNormSq H + 4 * frobNormSq (isoBlockTrace H) := by
  have ht0 := (frobNormSq_commPart_anticommPart_eq T0 H T0_symm T0_inv).1
  have ht1 := (frobNormSq_commPart_anticommPart_eq T1 H T1_symm T1_inv).1
  have ht2 := (frobNormSq_commPart_anticommPart_eq T2 H T2_symm T2_inv).1
  have ht3 := (frobNormSq_commPart_anticommPart_eq T3 H T3_symm T3_inv).1
  have hg0 := (frobNormSq_commPart_anticommPart_eq G0 H G0_symm G0_inv).1
  have hg1 := (frobNormSq_commPart_anticommPart_eq G1 H G1_symm G1_inv).1
  have hg2 := (frobNormSq_commPart_anticommPart_eq G2 H G2_symm G2_inv).1
  have hg3 := (frobNormSq_commPart_anticommPart_eq G3 H G3_symm G3_inv).1
  have hHaar := eight_involution_haar_projection H hH
  have hSumInner :
      frobInner H (T0 * H * T0) + frobInner H (T1 * H * T1) +
        frobInner H (T2 * H * T2) + frobInner H (T3 * H * T3) +
        frobInner H (G0 * H * G0) + frobInner H (G1 * H * G1) +
        frobInner H (G2 * H * G2) + frobInner H (G3 * H * G3) =
      8 * frobNormSq (isoBlockTrace H) := by
    have hLin :
        frobInner H (T0 * H * T0) + frobInner H (T1 * H * T1) +
          frobInner H (T2 * H * T2) + frobInner H (T3 * H * T3) +
          frobInner H (G0 * H * G0) + frobInner H (G1 * H * G1) +
          frobInner H (G2 * H * G2) + frobInner H (G3 * H * G3) =
        8 * frobInner H ((1 / 8 : ℝ) •
          (T0 * H * T0 + T1 * H * T1 + T2 * H * T2 + T3 * H * T3 +
           G0 * H * G0 + G1 * H * G1 + G2 * H * G2 + G3 * H * G3)) := by
      unfold frobInner
      rw [Matrix.mul_smul, trace_smul]
      simp only [Matrix.mul_add, trace_add, smul_eq_mul]
      ring
    rw [hLin, hHaar, frobInner_isoBlockTrace_self]
  linarith

/-- **Exact 8-Involution Byers–Nash Parseval Identity**:
For any `A : Mat6` and `K = skewWitness6 a b c`, with `H = symPart A K ∈ 𝕊_6`
and `Y = L_A(K) ∈ 𝕂_6`:
`∑_{r=0}^3 (‖L_A(K T_r)‖_F² + ‖L_A(K G_r)‖_F²) = 16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² + 4 ‖Y‖_F² + 4 ‖diagBlocks Y‖_F²`. -/
theorem eight_involution_byers_nash_identity (A : Mat6) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    frobNormSq (lyap A (K * T0)) + frobNormSq (lyap A (K * T1)) +
      frobNormSq (lyap A (K * T2)) + frobNormSq (lyap A (K * T3)) +
      frobNormSq (lyap A (K * G0)) + frobNormSq (lyap A (K * G1)) +
      frobNormSq (lyap A (K * G2)) + frobNormSq (lyap A (K * G3)) =
      16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) +
      4 * frobNormSq Y + 4 * frobNormSq (diagBlocks Y) := by
  intro K H Y
  have hK := skewWitness6_skew a b c
  have hY := lyap_skew_of_skew A K hK
  have hH_symm : Hᵀ = H := symPart_transpose A K hK
  have hT := (four_involution_parseval_decomposition A a b c).1
  have hG_orth := byers_nash_orthogonal_involutions A K G0 G1 G2 G3 hK
    G0_symm G0_inv (G0_anticomm_skewWitness6 a b c)
    G1_symm G1_inv (G1_anticomm_skewWitness6 a b c)
    G2_symm G2_inv (G2_anticomm_skewWitness6 a b c)
    G3_symm G3_inv (G3_anticomm_skewWitness6 a b c)
  have hG_pars := (klein_four_G_parseval_skew Y hY).2
  have hH_pars := eight_involution_parseval_identity H hH_symm
  dsimp [K, H, Y] at hT hG_orth hG_pars hH_pars ⊢
  linarith [hT, hG_orth, hG_pars, hH_pars]

/-- **8-Involution Dominance Criterion (`eight_involution_dominance_of_commutator_or_diag`)**:
For any `A : Mat6` and `K = skewWitness6 a b c`, with `H = symPart A K` and `Y = L_A(K)`:
1. The sum of excess gains over `‖Y‖_F²` across all 8 canonical symmetric comparators
   `{K T_r, K G_r}` equals `16 ‖H‖_F² + 16 ‖isoBlockTrace H‖_F² - 4 ‖offDiagBlocks Y‖_F²`.
2. Consequently, whenever `‖offDiagBlocks Y‖_F² ≤ 4 ‖H‖_F² + 4 ‖isoBlockTrace H‖_F²`,
   at least one of the 8 symmetric comparators `S ∈ {K T_0, ..., K T_3, K G_0, ..., K G_3}`
   satisfies `‖L_A(K)‖_F² ≤ ‖L_A(S)‖_F²` (with `‖S‖_F² = ‖K‖_F²`). -/
theorem eight_involution_dominance_of_commutator_or_diag (A : Mat6) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    (frobNormSq (lyap A (K * T0)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * T1)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * T2)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * T3)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G0)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G1)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G2)) - frobNormSq Y) +
      (frobNormSq (lyap A (K * G3)) - frobNormSq Y) =
      16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) -
        4 * frobNormSq (offDiagBlocks Y) ∧
    (frobNormSq (offDiagBlocks Y) ≤ 4 * frobNormSq H + 4 * frobNormSq (isoBlockTrace H) →
      frobNormSq Y ≤ frobNormSq (lyap A (K * T0)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * T1)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * T2)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * T3)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G0)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G1)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G2)) ∨
      frobNormSq Y ≤ frobNormSq (lyap A (K * G3))) := by
  intro K H Y
  have h8 := eight_involution_byers_nash_identity A a b c
  have hPyth := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  dsimp [K, H, Y] at h8 hPyth ⊢
  have hDiff :
      (frobNormSq (lyap A (K * T0)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * T1)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * T2)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * T3)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * G0)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * G1)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * G2)) - frobNormSq Y) +
        (frobNormSq (lyap A (K * G3)) - frobNormSq Y) =
        16 * frobNormSq H + 16 * frobNormSq (isoBlockTrace H) -
          4 * frobNormSq (offDiagBlocks Y) := by
    linarith [h8, hPyth]
  refine ⟨hDiff, fun hCond => ?_⟩
  by_cases h0 : frobNormSq Y ≤ frobNormSq (lyap A (K * T0))
  · exact Or.inl h0
  by_cases h1 : frobNormSq Y ≤ frobNormSq (lyap A (K * T1))
  · exact Or.inr (Or.inl h1)
  by_cases h2 : frobNormSq Y ≤ frobNormSq (lyap A (K * T2))
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : frobNormSq Y ≤ frobNormSq (lyap A (K * T3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : frobNormSq Y ≤ frobNormSq (lyap A (K * G0))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  by_cases h5 : frobNormSq Y ≤ frobNormSq (lyap A (K * G1))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  by_cases h6 : frobNormSq Y ≤ frobNormSq (lyap A (K * G2))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  right; right; right; right; right; right; right
  linarith [hDiff, hCond]

#print axioms symmetric_intertwiner_lyap_pairing
#print axioms symmetric_intertwiner_self_bound
#print axioms canonical_four_term_decomposition
#print axioms four_G_involutions_same_square
#print axioms eight_involution_haar_projection
#print axioms klein_four_G_parseval_skew
#print axioms eight_involution_parseval_identity
#print axioms eight_involution_byers_nash_identity
#print axioms eight_involution_dominance_of_commutator_or_diag

end
end Research.ByersNashHaarIntertwiner
