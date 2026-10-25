import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Research.ByersNashOffDiagComplete

/-!
# Byers–Nash `n = 6`: Extremality Constraints from Darboux Sign Flips

The comparator theorems of `Research.ByersNashOffDiagComplete` hold for an *arbitrary*
`K = skewWitness6 a b c`. Their dominance conclusions need the hypothesis
`‖offDiagBlocks Y‖_F² ≤ 4 ‖H‖_F² + 4 ‖isoBlockTrace H‖_F²` (`Y = L_A(K)`,
`H = symPart A K = (1/2)(A K - K Aᵀ)`), which fails for many `(A, K)`. Numerically it also
fails at the true skew maximizer of `‖L_A(Z)‖_F / ‖Z‖_F`. Any closing argument therefore has to use that `K` is
extremal. This module records the first such constraints:

1. `j_comm_bound_iff_offDiag_bound`: the `J`-commuting hypothesis of
   `twelve_comparator_dominance_of_j_comm_bound` (part 2) is equivalent to the original
   hypothesis above. The `J` / `{I₂, F, G}` split does not weaken it.
2. `flip1_normSq`, `flip2_normSq`, `flip3_normSq`: exact norm identities for the Lyapunov images
   of the three single-plane sign flips `diag(-aJ, bJ, cJ)`, `diag(aJ, -bJ, cJ)`,
   `diag(aJ, bJ, -cJ)`. Each one keeps `diagBlocks Y` and the untouched off-diagonal pair of `Y`,
   and replaces the two off-diagonal pairs that touch the flipped plane by `±2 H` on those pairs.
3. `IsSkewExtremal A K`: the division-free statement that `K` maximizes the skew Rayleigh
   quotient of `L_A`.
4. `extremal_flip_offDiag_bound`: at an extremal `K = skewWitness6 a b c`, each plane satisfies
   `4 (‖H_{pq}‖² + ‖H_{pr}‖²) ≤ ‖Y_{pq}‖² + ‖Y_{pr}‖²`, hence
   `4 ‖offDiagBlocks H‖_F² ≤ ‖offDiagBlocks Y‖_F²`.
5. `extremal_eight_comparator_excess_le`: at an extremal `K`, the total excess of the 8
   same-square comparators `{K T_r, K G_r}` over `‖Y‖_F²` is at most
   `16 (‖diagBlocks H‖_F² + ‖isoBlockTrace H‖_F²)`. So only the block-diagonal part of `H` can
   make the 8-comparator mean argument work.

This module does not prove `k(A) ≤ s(A)` for `n = 6`.
-/

namespace Research.ByersNashExtremalFlip

open Matrix BigOperators
open Research.ByersNashDuality
open Research.ByersNashMultiTerm
open Research.ByersNashHaarIntertwiner
open Research.ByersNashOffDiagComplete

noncomputable section

lemma frobNormSq_eq_sum_sq {n : Type*} [Fintype n] (X : Matrix n n ℝ) :
    frobNormSq X = ∑ i, ∑ j, X i j ^ 2 := by
  unfold frobNormSq frobInner Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Entrywise Lyapunov image of a sign-flipped skew matrix. -/
lemma lyap_signFlip_apply (A K : Mat6) (σ : Fin 6 → ℝ)
    (hR : ∀ i j, (A * (K * Matrix.diagonal σ)) i j = (A * K) i j * σ j)
    (hL : ∀ i j, ((Matrix.diagonal σ * K) * Aᵀ) i j = σ i * (K * Aᵀ) i j)
    (K' : Mat6) (h1 : K' = K * Matrix.diagonal σ) (h2 : K' = Matrix.diagonal σ * K) (i j : Fin 6) :
    (lyap A K') i j = (A * K) i j * σ j + σ i * (K * Aᵀ) i j := by
  unfold lyap
  rw [Matrix.add_apply]
  have e1 : (A * K') i j = (A * K) i j * σ j := by rw [h1, hR]
  have e2 : (K' * Aᵀ) i j = σ i * (K * Aᵀ) i j := by rw [h2, hL]
  rw [e1, e2]

/-- Sign pattern flipping Darboux plane `1`. -/
def flipSign1 : Fin 6 → ℝ := ![-1, -1, 1, 1, 1, 1]

lemma skewWitness6_flip1_right (a b c : ℝ) :
    skewWitness6 (-a) b c = skewWitness6 a b c * Matrix.diagonal flipSign1 := by
  ext i j; rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, flipSign1]

lemma skewWitness6_flip1_left (a b c : ℝ) :
    skewWitness6 (-a) b c = Matrix.diagonal flipSign1 * skewWitness6 a b c := by
  ext i j; rw [Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, flipSign1]

private lemma flip1_entry (A : Mat6) (a b c : ℝ) (i j : Fin 6) :
    (lyap A (skewWitness6 (-a) b c)) i j ^ 2 =
      (diagBlocks (lyap A (skewWitness6 a b c))) i j ^ 2 +
      (blockPair23 (lyap A (skewWitness6 a b c))) i j ^ 2 +
      4 * (blockPair12 (symPart A (skewWitness6 a b c))) i j ^ 2 +
      4 * (blockPair13 (symPart A (skewWitness6 a b c))) i j ^ 2 := by
  set K := skewWitness6 a b c with hK
  have hL := lyap_signFlip_apply A K flipSign1
    (fun i j => by rw [← Matrix.mul_assoc, Matrix.mul_diagonal])
    (fun i j => by rw [Matrix.mul_assoc, Matrix.diagonal_mul])
    (skewWitness6 (-a) b c) (skewWitness6_flip1_right a b c) (skewWitness6_flip1_left a b c) i j
  have hY : (lyap A K) i j = (A * K) i j + (K * Aᵀ) i j := by
    unfold lyap; rw [Matrix.add_apply]
  have hH : (symPart A K) i j = (1 / 2 : ℝ) * ((A * K) i j - (K * Aᵀ) i j) := by
    unfold symPart; rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [hL]
  simp only [diagBlocks, blockPair12, blockPair13, blockPair23, Matrix.of_apply]
  rw [hY, hH]
  generalize (A * K) i j = u
  generalize (K * Aᵀ) i j = v
  fin_cases i <;> fin_cases j <;> simp [flipSign1, planeOf] <;> ring

/-- Sign pattern flipping Darboux plane `2`. -/
def flipSign2 : Fin 6 → ℝ := ![1, 1, -1, -1, 1, 1]

lemma skewWitness6_flip2_right (a b c : ℝ) :
    skewWitness6 a (-b) c = skewWitness6 a b c * Matrix.diagonal flipSign2 := by
  ext i j; rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, flipSign2]

lemma skewWitness6_flip2_left (a b c : ℝ) :
    skewWitness6 a (-b) c = Matrix.diagonal flipSign2 * skewWitness6 a b c := by
  ext i j; rw [Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, flipSign2]

private lemma flip2_entry (A : Mat6) (a b c : ℝ) (i j : Fin 6) :
    (lyap A (skewWitness6 a (-b) c)) i j ^ 2 =
      (diagBlocks (lyap A (skewWitness6 a b c))) i j ^ 2 +
      (blockPair13 (lyap A (skewWitness6 a b c))) i j ^ 2 +
      4 * (blockPair12 (symPart A (skewWitness6 a b c))) i j ^ 2 +
      4 * (blockPair23 (symPart A (skewWitness6 a b c))) i j ^ 2 := by
  set K := skewWitness6 a b c with hK
  have hL := lyap_signFlip_apply A K flipSign2
    (fun i j => by rw [← Matrix.mul_assoc, Matrix.mul_diagonal])
    (fun i j => by rw [Matrix.mul_assoc, Matrix.diagonal_mul])
    (skewWitness6 a (-b) c) (skewWitness6_flip2_right a b c) (skewWitness6_flip2_left a b c) i j
  have hY : (lyap A K) i j = (A * K) i j + (K * Aᵀ) i j := by
    unfold lyap; rw [Matrix.add_apply]
  have hH : (symPart A K) i j = (1 / 2 : ℝ) * ((A * K) i j - (K * Aᵀ) i j) := by
    unfold symPart; rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [hL]
  simp only [diagBlocks, blockPair12, blockPair13, blockPair23, Matrix.of_apply]
  rw [hY, hH]
  generalize (A * K) i j = u
  generalize (K * Aᵀ) i j = v
  fin_cases i <;> fin_cases j <;> simp [flipSign2, planeOf] <;> ring

/-- Sign pattern flipping Darboux plane `3`. -/
def flipSign3 : Fin 6 → ℝ := ![1, 1, 1, 1, -1, -1]

lemma skewWitness6_flip3_right (a b c : ℝ) :
    skewWitness6 a b (-c) = skewWitness6 a b c * Matrix.diagonal flipSign3 := by
  ext i j; rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, flipSign3]

lemma skewWitness6_flip3_left (a b c : ℝ) :
    skewWitness6 a b (-c) = Matrix.diagonal flipSign3 * skewWitness6 a b c := by
  ext i j; rw [Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [skewWitness6, flipSign3]

private lemma flip3_entry (A : Mat6) (a b c : ℝ) (i j : Fin 6) :
    (lyap A (skewWitness6 a b (-c))) i j ^ 2 =
      (diagBlocks (lyap A (skewWitness6 a b c))) i j ^ 2 +
      (blockPair12 (lyap A (skewWitness6 a b c))) i j ^ 2 +
      4 * (blockPair13 (symPart A (skewWitness6 a b c))) i j ^ 2 +
      4 * (blockPair23 (symPart A (skewWitness6 a b c))) i j ^ 2 := by
  set K := skewWitness6 a b c with hK
  have hL := lyap_signFlip_apply A K flipSign3
    (fun i j => by rw [← Matrix.mul_assoc, Matrix.mul_diagonal])
    (fun i j => by rw [Matrix.mul_assoc, Matrix.diagonal_mul])
    (skewWitness6 a b (-c)) (skewWitness6_flip3_right a b c) (skewWitness6_flip3_left a b c) i j
  have hY : (lyap A K) i j = (A * K) i j + (K * Aᵀ) i j := by
    unfold lyap; rw [Matrix.add_apply]
  have hH : (symPart A K) i j = (1 / 2 : ℝ) * ((A * K) i j - (K * Aᵀ) i j) := by
    unfold symPart; rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [hL]
  simp only [diagBlocks, blockPair12, blockPair13, blockPair23, Matrix.of_apply]
  rw [hY, hH]
  generalize (A * K) i j = u
  generalize (K * Aᵀ) i j = v
  fin_cases i <;> fin_cases j <;> simp [flipSign3, planeOf] <;> ring

/-! ## Norm identities for the three single-plane Darboux flips -/

/-- `‖L_A(diag(-aJ, bJ, cJ))‖_F² = ‖diagBlocks Y‖² + ‖Y₂₃‖² + 4‖H₁₂‖² + 4‖H₁₃‖²`. -/
theorem flip1_normSq (A : Mat6) (a b c : ℝ) :
    frobNormSq (lyap A (skewWitness6 (-a) b c)) =
      frobNormSq (diagBlocks (lyap A (skewWitness6 a b c))) +
      frobNormSq (blockPair23 (lyap A (skewWitness6 a b c))) +
      4 * frobNormSq (blockPair12 (symPart A (skewWitness6 a b c))) +
      4 * frobNormSq (blockPair13 (symPart A (skewWitness6 a b c))) := by
  simp only [frobNormSq_eq_sum_sq, flip1_entry, Finset.sum_add_distrib, Finset.mul_sum]

/-- `‖L_A(diag(aJ, -bJ, cJ))‖_F² = ‖diagBlocks Y‖² + ‖Y₁₃‖² + 4‖H₁₂‖² + 4‖H₂₃‖²`. -/
theorem flip2_normSq (A : Mat6) (a b c : ℝ) :
    frobNormSq (lyap A (skewWitness6 a (-b) c)) =
      frobNormSq (diagBlocks (lyap A (skewWitness6 a b c))) +
      frobNormSq (blockPair13 (lyap A (skewWitness6 a b c))) +
      4 * frobNormSq (blockPair12 (symPart A (skewWitness6 a b c))) +
      4 * frobNormSq (blockPair23 (symPart A (skewWitness6 a b c))) := by
  simp only [frobNormSq_eq_sum_sq, flip2_entry, Finset.sum_add_distrib, Finset.mul_sum]

/-- `‖L_A(diag(aJ, bJ, -cJ))‖_F² = ‖diagBlocks Y‖² + ‖Y₁₂‖² + 4‖H₁₃‖² + 4‖H₂₃‖²`. -/
theorem flip3_normSq (A : Mat6) (a b c : ℝ) :
    frobNormSq (lyap A (skewWitness6 a b (-c))) =
      frobNormSq (diagBlocks (lyap A (skewWitness6 a b c))) +
      frobNormSq (blockPair12 (lyap A (skewWitness6 a b c))) +
      4 * frobNormSq (blockPair13 (symPart A (skewWitness6 a b c))) +
      4 * frobNormSq (blockPair23 (symPart A (skewWitness6 a b c))) := by
  simp only [frobNormSq_eq_sum_sq, flip3_entry, Finset.sum_add_distrib, Finset.mul_sum]

lemma frobNormSq_skewWitness6 (a b c : ℝ) :
    frobNormSq (skewWitness6 a b c) = 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [frobNormSq_eq_sum_sq]
  simp [skewWitness6, Fin.sum_univ_succ]
  ring

/-! ## Skew extremality -/

/-- `K` is a skew-symmetric maximizer of the Rayleigh quotient `‖L_A(Z)‖_F² / ‖Z‖_F²` over
`𝕂_n`, stated without division: `‖L_A(Z)‖² ‖K‖² ≤ ‖L_A(K)‖² ‖Z‖²` for every skew `Z`. -/
def IsSkewExtremal {n : Type*} [Fintype n] (A K : Matrix n n ℝ) : Prop :=
  Kᵀ = -K ∧ ∀ Z : Matrix n n ℝ, Zᵀ = -Z →
    frobNormSq (lyap A Z) * frobNormSq K ≤ frobNormSq (lyap A K) * frobNormSq Z

/-- An extremal skew `K` dominates every skew `Z` of the same Frobenius norm. -/
lemma IsSkewExtremal.le_of_normSq_eq {n : Type*} [Fintype n] {A K : Matrix n n ℝ}
    (hK : IsSkewExtremal A K) (Z : Matrix n n ℝ) (hZ : Zᵀ = -Z)
    (hN : frobNormSq Z = frobNormSq K) :
    frobNormSq (lyap A Z) ≤ frobNormSq (lyap A K) := by
  have h := hK.2 Z hZ
  rw [hN] at h
  rcases (frobNormSq_nonneg_gen K).lt_or_eq with hpos | hzero
  · exact le_of_mul_le_mul_right h hpos
  · -- `‖K‖² = 0` forces `K = 0` and `Z = 0`, hence both images vanish.
    have hK0 : K = 0 := by
      ext i j
      have hs := frobNormSq_eq_sum_sq K
      rw [← hzero] at hs
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, K i j ^ 2 :=
        fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs.symm i (Finset.mem_univ _)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (K i j))).1 hi j
        (Finset.mem_univ _)
      simpa using hj
    have hZ0 : Z = 0 := by
      ext i j
      have hs := frobNormSq_eq_sum_sq Z
      rw [hN, ← hzero] at hs
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ ∑ j, Z i j ^ 2 :=
        fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs.symm i (Finset.mem_univ _)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (Z i j))).1 hi j
        (Finset.mem_univ _)
      simpa using hj
    subst hK0; subst hZ0; exact le_refl _

/-! ## Main theorem: extremality bounds the off-diagonal symmetric part `H` -/

/-- **Darboux sign-flip extremality bound (`extremal_flip_offDiag_bound`)**:
Let `K = skewWitness6 a b c`, `Y = L_A(K)`, `H = symPart A K = (1/2)(A K - K Aᵀ)`, and suppose
`K` maximizes `‖L_A(Z)‖_F² / ‖Z‖_F²` over skew `Z`. Comparing `K` with the three same-norm
plane flips `diag(-aJ, bJ, cJ)`, `diag(aJ, -bJ, cJ)`, `diag(aJ, bJ, -cJ)` gives, for each plane,
1. `4 (‖H₁₂‖² + ‖H₁₃‖²) ≤ ‖Y₁₂‖² + ‖Y₁₃‖²`,
2. `4 (‖H₁₂‖² + ‖H₂₃‖²) ≤ ‖Y₁₂‖² + ‖Y₂₃‖²`,
3. `4 (‖H₁₃‖² + ‖H₂₃‖²) ≤ ‖Y₁₃‖² + ‖Y₂₃‖²`,
and hence `4 ‖offDiagBlocks H‖_F² ≤ ‖offDiagBlocks Y‖_F²`. Here `X_{pq} = blockPair_{pq} X`. -/
theorem extremal_flip_offDiag_bound (A : Mat6) (a b c : ℝ)
    (hExt : IsSkewExtremal A (skewWitness6 a b c)) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    4 * (frobNormSq (blockPair12 H) + frobNormSq (blockPair13 H)) ≤
      frobNormSq (blockPair12 Y) + frobNormSq (blockPair13 Y) ∧
    4 * (frobNormSq (blockPair12 H) + frobNormSq (blockPair23 H)) ≤
      frobNormSq (blockPair12 Y) + frobNormSq (blockPair23 Y) ∧
    4 * (frobNormSq (blockPair13 H) + frobNormSq (blockPair23 H)) ≤
      frobNormSq (blockPair13 Y) + frobNormSq (blockPair23 Y) ∧
    4 * frobNormSq (offDiagBlocks H) ≤ frobNormSq (offDiagBlocks Y) := by
  intro K H Y
  have hN1 : frobNormSq (skewWitness6 (-a) b c) = frobNormSq K := by
    simp only [K, frobNormSq_skewWitness6]; ring
  have hN2 : frobNormSq (skewWitness6 a (-b) c) = frobNormSq K := by
    simp only [K, frobNormSq_skewWitness6]; ring
  have hN3 : frobNormSq (skewWitness6 a b (-c)) = frobNormSq K := by
    simp only [K, frobNormSq_skewWitness6]; ring
  have e1 := hExt.le_of_normSq_eq _ (skewWitness6_skew (-a) b c) hN1
  have e2 := hExt.le_of_normSq_eq _ (skewWitness6_skew a (-b) c) hN2
  have e3 := hExt.le_of_normSq_eq _ (skewWitness6_skew a b (-c)) hN3
  rw [flip1_normSq] at e1
  rw [flip2_normSq] at e2
  rw [flip3_normSq] at e3
  have hY := frobNormSq_eq_diagBlocks_add_offDiagBlocks Y
  have hYo := frobNormSq_offDiagBlocks_eq_sum_blockPairs Y
  have hHo := frobNormSq_offDiagBlocks_eq_sum_blockPairs H
  dsimp only [K, H, Y] at e1 e2 e3 hY hYo hHo ⊢
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Obstruction for the 8-comparator route at an extremal `K`
(`extremal_eight_comparator_excess_le`)**: if `K = skewWitness6 a b c` is a skew extremal for
`L_A`, the total excess of the 8 same-square comparators `{K T_r, K G_r}` over `‖Y‖_F²`
(computed exactly by `eight_involution_dominance_of_commutator_or_diag`) is at most
`16 (‖diagBlocks H‖_F² + ‖isoBlockTrace H‖_F²)`. In particular the off-diagonal part of `H`
can never pay for the off-diagonal part of `Y` at an extremal point; only the block-diagonal
part of `H` can. -/
theorem extremal_eight_comparator_excess_le (A : Mat6) (a b c : ℝ)
    (hExt : IsSkewExtremal A (skewWitness6 a b c)) :
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
      (frobNormSq (lyap A (K * G3)) - frobNormSq Y) ≤
      16 * (frobNormSq (diagBlocks H) + frobNormSq (isoBlockTrace H)) := by
  intro K H Y
  have hD := (eight_involution_dominance_of_commutator_or_diag A a b c).1
  have hB := (extremal_flip_offDiag_bound A a b c hExt).2.2.2
  have hH := frobNormSq_eq_diagBlocks_add_offDiagBlocks H
  dsimp only [K, H, Y] at hD hB hH ⊢
  rw [hD]
  linarith

/-- The `J`-commuting hypothesis of `twelve_comparator_dominance_of_j_comm_bound` (part 2) is
literally equivalent to the original 8-comparator hypothesis
`‖offDiagBlocks Y‖² ≤ 4 ‖H‖² + 4 ‖isoBlockTrace H‖²` of
`eight_involution_dominance_of_commutator_or_diag`: the `J`/`{I₂,F,G}` split is a relabelling,
not a weakening. -/
theorem j_comm_bound_iff_offDiag_bound (A : Mat6) (a b c : ℝ) :
    let K := skewWitness6 a b c
    let H := symPart A K
    let Y := lyap A K
    (offDiagCommJEnergy Y ≤
        4 * frobNormSq H + 4 * frobNormSq (isoBlockTrace H) - offDiagAnticommEnergy Y) ↔
      frobNormSq (offDiagBlocks Y) ≤ 4 * frobNormSq H + 4 * frobNormSq (isoBlockTrace H) := by
  intro K H Y
  have h := (frobNormSq_offDiagBlocks_eq_anticomm_add_commJ Y).1
  constructor <;> intro h' <;> linarith

#print axioms extremal_flip_offDiag_bound
#print axioms extremal_eight_comparator_excess_le
#print axioms j_comm_bound_iff_offDiag_bound

end
end Research.ByersNashExtremalFlip
