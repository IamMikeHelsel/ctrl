/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Linear Least Squares, Weighted Least Squares and Recursive Least Squares

Least squares is the backbone of sensor calibration and system identification. Over `ℝ`, with
design matrix $A \in \mathbb{R}^{m \times n}$, observations $b \in \mathbb{R}^m$ and an optional
weight $W$, we study the costs
$$J(x) = \|A x - b\|^2 \quad (`rss`), \qquad J_W(x) = (A x - b)^\top W (A x - b) \quad (`wrss`).$$

## Main results

1. **Normal equations** (`isLeastSquares_iff`): $x$ minimises $\|A y - b\|^2$ over all $y$ iff
   $A^\top A x = A^\top b$. The proof rests on the exact Pythagorean decomposition
   (`rss_eq_add_of_normal`): if $A^\top A x = A^\top b$ then for every $y$
   $$\|A y - b\|^2 = \|A x - b\|^2 + \|A (y - x)\|^2.$$
   `rss_eq_norm_sq` identifies `rss` with the squared Euclidean norm.
2. **Full column rank** (`det_transpose_mul_self_ne_zero`,
   `isLeastSquares_iff_eq_inv_of_injective`): if $y \mapsto A y$ is injective then $A^\top A$
   is invertible and the minimiser is unique, equal to $(A^\top A)^{-1} A^\top b$.
   `isLeastSquares_iff_eq_inv` states the same under the hypothesis that $A^\top A$ is
   invertible.
3. **Weighted least squares** (`isWeightedLeastSquares_iff`): for $W \succeq 0$, $x$ minimises
   $J_W$ iff $A^\top W A x = A^\top W b$ (decomposition: `wrss_eq_add_of_normal`). With
   $W \succ 0$ and $A$ of full column rank, the minimiser is unique and equals
   $(A^\top W A)^{-1} A^\top W b$ (`isWeightedLeastSquares_iff_eq_inv_of_injective`).
4. **Sherman–Morrison and recursive least squares**, over any field $K$:
   * `mul_shermanMorrison`, `shermanMorrison_mul`: if $Y P = 1$ and $1 + a^\top P a \ne 0$, then
     $P^+ = P - \dfrac{P a a^\top P}{1 + a^\top P a}$ is the two-sided inverse of $Y + a a^\top$.
   * `shermanMorrison_mulVec`: the RLS gain is $P^+ a = P a / (1 + a^\top P a)$.
   * `rlsUpdate_normal`: if $Y x = r$, then $x^+ = x + P^+ a (\beta - a^\top x)$ satisfies
     $(Y + a a^\top) x^+ = r + \beta a$ (the augmented normal equations in information form).
   * `rlsUpdate_isLeastSquares` (over `ℝ`): if $x$ is a least-squares solution for $(A, b)$ and
     $(A^\top A) P = 1$, then $x^+$ is a least-squares solution for the data set with the extra
     row $(a^\top, \beta)$ appended. Here $1 + a^\top P a > 0$ is derived, not assumed.
5. **Straight-line fit** $y \approx c_0 + c_1 t$ (`lineFit_isMin_iff`, `lineFit_isMin_iff_eq`):
   $(c_0, c_1)$ minimises $\sum_i (c_0 + c_1 t_i - y_i)^2$ iff
   $c_0 N + c_1 \sum t_i = \sum y_i$ and $c_0 \sum t_i + c_1 \sum t_i^2 = \sum t_i y_i$; when
   $D = N \sum t_i^2 - (\sum t_i)^2 \ne 0$ the unique minimiser is
   $c_1 = (N \sum t_i y_i - \sum t_i \sum y_i) / D$,
   $c_0 = (\sum t_i^2 \sum y_i - \sum t_i \sum t_i y_i) / D$.

## References

* Gauss, C. F. (1809). *Theoria Motus Corporum Coelestium*.
* Sherman, J., & Morrison, W. J. (1950). Adjustment of an Inverse Matrix to Changes in a
  Specified Column or Row of the Original Matrix. *Annals of Math. Stat.*, 21(1), 124–127.
* Ljung, L. (1999). *System Identification: Theory for the User*, 2nd ed. Prentice Hall.
* Kailath, T., Sayed, A. H., & Hassibi, B. (2000). *Linear Estimation*. Prentice Hall.
-/

namespace ControlsLean.Estimation

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Weighted residual sum of squares `(A x - b)ᵀ W (A x - b)`. -/
def wrss (W : Matrix m m ℝ) (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : ℝ :=
  (A *ᵥ x - b) ⬝ᵥ (W *ᵥ (A *ᵥ x - b))

private lemma dotProduct_mulVec_symm {W : Matrix m m ℝ} (hW : Wᵀ = W) (u v : m → ℝ) :
    u ⬝ᵥ (W *ᵥ v) = v ⬝ᵥ (W *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]

private lemma mulVec_dotProduct_eq (A : Matrix m n ℝ) (d : n → ℝ) (u : m → ℝ) :
    (A *ᵥ d) ⬝ᵥ u = d ⬝ᵥ (Aᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

private lemma transpose_mulVec_weighted_residual (W : Matrix m m ℝ) (A : Matrix m n ℝ)
    (b : m → ℝ) (x : n → ℝ) :
    Aᵀ *ᵥ (W *ᵥ (A *ᵥ x - b)) = (Aᵀ * W * A) *ᵥ x - (Aᵀ * W) *ᵥ b := by
  rw [mulVec_sub, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- Exact quadratic expansion of the weighted cost along a direction `d` (for symmetric `W`):
`J(x + d) = J(x) + 2 dᵀ (Aᵀ W A x - Aᵀ W b) + (A d)ᵀ W (A d)`. -/
theorem wrss_add {W : Matrix m m ℝ} (hW : Wᵀ = W) (A : Matrix m n ℝ) (b : m → ℝ)
    (x d : n → ℝ) :
    wrss W A b (x + d) = wrss W A b x +
      2 * (d ⬝ᵥ ((Aᵀ * W * A) *ᵥ x - (Aᵀ * W) *ᵥ b)) + (A *ᵥ d) ⬝ᵥ (W *ᵥ (A *ᵥ d)) := by
  unfold wrss
  have h1 : A *ᵥ (x + d) - b = (A *ᵥ x - b) + A *ᵥ d := by rw [mulVec_add]; abel
  rw [h1, ← transpose_mulVec_weighted_residual, ← mulVec_dotProduct_eq]
  have h2 := dotProduct_mulVec_symm hW (A *ᵥ x - b) (A *ᵥ d)
  simp only [mulVec_add, dotProduct_add, add_dotProduct] at h2 ⊢
  rw [h2]
  ring

/-- **Weighted Pythagorean decomposition.** If `x` solves `Aᵀ W A x = Aᵀ W b` and `Wᵀ = W`,
then for every `y`, `J(y) = J(x) + (A (y - x))ᵀ W (A (y - x))`. -/
theorem wrss_eq_add_of_normal {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m n ℝ}
    {b : m → ℝ} {x : n → ℝ} (hx : (Aᵀ * W * A) *ᵥ x = (Aᵀ * W) *ᵥ b) (y : n → ℝ) :
    wrss W A b y = wrss W A b x + (A *ᵥ (y - x)) ⬝ᵥ (W *ᵥ (A *ᵥ (y - x))) := by
  have := wrss_add hW A b x (y - x)
  rwa [add_sub_cancel, hx, sub_self, dotProduct_zero, mul_zero, add_zero] at this

private lemma eq_zero_of_forall_nonneg {G q : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * G + t ^ 2 * q) :
    G = 0 := by
  have h1 := h 1
  have h2 := h (-1)
  have hq : 0 ≤ q := by nlinarith
  set t := -G / (q + 1) with ht_def
  have ht : G = -(t * (q + 1)) := by
    rw [ht_def]; field_simp
  have h3 := h t
  rw [ht] at h3
  have ht0 : t = 0 := by nlinarith [sq_nonneg t]
  rw [ht, ht0]; ring

/-- First-order condition: any global minimiser of the weighted cost (with `Wᵀ = W`) solves the
weighted normal equations `Aᵀ W A x = Aᵀ W b`. -/
theorem normal_of_forall_wrss_le {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m n ℝ}
    {b : m → ℝ} {x : n → ℝ} (hmin : ∀ y, wrss W A b x ≤ wrss W A b y) :
    (Aᵀ * W * A) *ᵥ x = (Aᵀ * W) *ᵥ b := by
  set g := (Aᵀ * W * A) *ᵥ x - (Aᵀ * W) *ᵥ b with hg
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (g ⬝ᵥ g) + t ^ 2 * ((A *ᵥ g) ⬝ᵥ (W *ᵥ (A *ᵥ g))) := by
    intro t
    have := hmin (x + t • g)
    rw [wrss_add hW, mulVec_smul, smul_dotProduct, smul_eq_mul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    nlinarith
  have hgg : g ⬝ᵥ g = 0 := eq_zero_of_forall_nonneg key
  rw [dotProduct_self_eq_zero, hg, sub_eq_zero] at hgg
  exact hgg

omit [Fintype m] in
private lemma transpose_eq_of_posSemidef {W : Matrix m m ℝ} (hW : W.PosSemidef) : Wᵀ = W := by
  ext i j
  have := congrFun (congrFun hW.1 i) j
  simpa [conjTranspose_apply] using this

private lemma quad_nonneg_of_posSemidef {W : Matrix m m ℝ} (hW : W.PosSemidef) (v : m → ℝ) :
    0 ≤ v ⬝ᵥ (W *ᵥ v) := by
  simpa using hW.dotProduct_mulVec_nonneg v

/-- `x` is a weighted least-squares solution: it minimises `(A y - b)ᵀ W (A y - b)`. -/
def IsWeightedLeastSquares (W : Matrix m m ℝ) (A : Matrix m n ℝ) (b : m → ℝ)
    (x : n → ℝ) : Prop :=
  ∀ y, wrss W A b x ≤ wrss W A b y

/-- **Weighted least squares.** For `W ⪰ 0`, `x` minimises `(A y - b)ᵀ W (A y - b)` iff
`Aᵀ W A x = Aᵀ W b`. -/
theorem isWeightedLeastSquares_iff {W : Matrix m m ℝ} (hW : W.PosSemidef)
    {A : Matrix m n ℝ} {b : m → ℝ} {x : n → ℝ} :
    IsWeightedLeastSquares W A b x ↔ (Aᵀ * W * A) *ᵥ x = (Aᵀ * W) *ᵥ b := by
  have hWt := transpose_eq_of_posSemidef hW
  refine ⟨normal_of_forall_wrss_le hWt, fun hx y => ?_⟩
  rw [wrss_eq_add_of_normal hWt hx y]
  linarith [quad_nonneg_of_posSemidef hW (A *ᵥ (y - x))]

/-! ### Ordinary least squares -/

/-- Residual sum of squares `‖A x - b‖² = (A x - b) ⬝ (A x - b)`. -/
def rss (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : ℝ :=
  (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)

/-- The residual sum of squares is `∑ᵢ ((A x)ᵢ - bᵢ)²`. -/
theorem rss_eq_sum_sq (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) :
    rss A b x = ∑ i, (A *ᵥ x - b) i ^ 2 := by
  simp [rss, dotProduct, sq]

/-- The residual sum of squares is the squared Euclidean norm `‖A x - b‖₂²`. -/
theorem rss_eq_norm_sq (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) :
    rss A b x = ‖(WithLp.toLp 2 (A *ᵥ x - b) : EuclideanSpace ℝ m)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, rss_eq_sum_sq]

private lemma rss_eq_wrss_one [DecidableEq m] (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) :
    rss A b x = wrss 1 A b x := by
  simp [rss, wrss]

/-- `x` is an (ordinary) least-squares solution: it minimises `‖A y - b‖²`. -/
def IsLeastSquares (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  ∀ y, rss A b x ≤ rss A b y

/-- **Pythagorean decomposition.** If `Aᵀ A x = Aᵀ b`, then for every `y`,
`‖A y - b‖² = ‖A x - b‖² + ‖A (y - x)‖²`. -/
theorem rss_eq_add_of_normal {A : Matrix m n ℝ} {b : m → ℝ} {x : n → ℝ}
    (hx : (Aᵀ * A) *ᵥ x = Aᵀ *ᵥ b) (y : n → ℝ) :
    rss A b y = rss A b x + (A *ᵥ (y - x)) ⬝ᵥ (A *ᵥ (y - x)) := by
  classical
  have h := wrss_eq_add_of_normal (W := (1 : Matrix m m ℝ)) transpose_one
    (by simpa using hx) y
  simpa [← rss_eq_wrss_one] using h

/-- **Normal equations.** `x` minimises `‖A y - b‖²` over all `y` iff `Aᵀ A x = Aᵀ b`. -/
theorem isLeastSquares_iff {A : Matrix m n ℝ} {b : m → ℝ} {x : n → ℝ} :
    IsLeastSquares A b x ↔ (Aᵀ * A) *ᵥ x = Aᵀ *ᵥ b := by
  classical
  have h := isWeightedLeastSquares_iff (W := (1 : Matrix m m ℝ)) PosSemidef.one
    (A := A) (b := b) (x := x)
  simpa [IsWeightedLeastSquares, IsLeastSquares, ← rss_eq_wrss_one] using h

/-! ### Full column rank: uniqueness and the closed form -/

section FullRank

variable [DecidableEq n]

private lemma mulVec_eq_iff_eq_inv {M : Matrix n n ℝ} (h : IsUnit M.det) (x c : n → ℝ) :
    M *ᵥ x = c ↔ x = M⁻¹ *ᵥ c := by
  constructor
  · rintro rfl
    rw [mulVec_mulVec, nonsing_inv_mul _ h, one_mulVec]
  · rintro rfl
    rw [mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]

omit [DecidableEq n] in
private lemma quad_gram (W : Matrix m m ℝ) (A : Matrix m n ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((Aᵀ * W * A) *ᵥ v) = (A *ᵥ v) ⬝ᵥ (W *ᵥ (A *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_dotProduct_eq]

/-- If `A` has full column rank (`y ↦ A y` injective) and `W ≻ 0`, then `Aᵀ W A` is
invertible. -/
theorem det_transpose_mul_weight_mul_ne_zero {W : Matrix m m ℝ} (hW : W.PosDef)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) : (Aᵀ * W * A).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_eq_zero_iff.mpr h
  have hAv : A *ᵥ v ≠ 0 := fun h0 => hv (hA (h0.trans (mulVec_zero A).symm))
  have hpos := (posDef_iff_dotProduct_mulVec.mp hW).2 hAv
  rw [star_trivial, ← quad_gram, hMv, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

/-- If `A` has full column rank (`y ↦ A y` injective), the Gram matrix `Aᵀ A` is invertible. -/
theorem det_transpose_mul_self_ne_zero {A : Matrix m n ℝ}
    (hA : Function.Injective A.mulVec) : (Aᵀ * A).det ≠ 0 := by
  classical
  simpa using det_transpose_mul_weight_mul_ne_zero PosDef.one hA

/-- With `W ⪰ 0` and `Aᵀ W A` invertible, the weighted least-squares solution is unique and
equals `(Aᵀ W A)⁻¹ Aᵀ W b`. -/
theorem isWeightedLeastSquares_iff_eq_inv {W : Matrix m m ℝ} (hW : W.PosSemidef)
    {A : Matrix m n ℝ} (h : IsUnit (Aᵀ * W * A).det) (b : m → ℝ) (x : n → ℝ) :
    IsWeightedLeastSquares W A b x ↔ x = (Aᵀ * W * A)⁻¹ *ᵥ ((Aᵀ * W) *ᵥ b) := by
  rw [isWeightedLeastSquares_iff hW, mulVec_eq_iff_eq_inv h]

/-- With `Aᵀ A` invertible, the least-squares solution is unique and equals `(Aᵀ A)⁻¹ Aᵀ b`. -/
theorem isLeastSquares_iff_eq_inv {A : Matrix m n ℝ} (h : IsUnit (Aᵀ * A).det)
    (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquares A b x ↔ x = (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b) := by
  rw [isLeastSquares_iff, mulVec_eq_iff_eq_inv h]

/-- **Full column rank.** If `y ↦ A y` is injective, the least-squares solution is unique and
equals `(Aᵀ A)⁻¹ Aᵀ b`. -/
theorem isLeastSquares_iff_eq_inv_of_injective {A : Matrix m n ℝ}
    (hA : Function.Injective A.mulVec) (b : m → ℝ) (x : n → ℝ) :
    IsLeastSquares A b x ↔ x = (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b) :=
  isLeastSquares_iff_eq_inv (isUnit_iff_ne_zero.mpr (det_transpose_mul_self_ne_zero hA)) b x

/-- **Weighted, full column rank.** If `W ≻ 0` and `y ↦ A y` is injective, the weighted
least-squares solution is unique and equals `(Aᵀ W A)⁻¹ Aᵀ W b`. -/
theorem isWeightedLeastSquares_iff_eq_inv_of_injective {W : Matrix m m ℝ} (hW : W.PosDef)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) (b : m → ℝ) (x : n → ℝ) :
    IsWeightedLeastSquares W A b x ↔ x = (Aᵀ * W * A)⁻¹ *ᵥ ((Aᵀ * W) *ᵥ b) :=
  isWeightedLeastSquares_iff_eq_inv hW.posSemidef
    (isUnit_iff_ne_zero.mpr (det_transpose_mul_weight_mul_ne_zero hW hA)) b x

end FullRank

/-! ### Sherman–Morrison and recursive least squares -/

section RLS

variable {K : Type*} [Field K] [DecidableEq n]

/-- Sherman–Morrison candidate `P⁺ = P - P a aᵀ P / (1 + aᵀ P a)`. -/
def shermanMorrison (P : Matrix n n K) (a : n → K) : Matrix n n K :=
  P - (1 + a ⬝ᵥ (P *ᵥ a))⁻¹ • vecMulVec (P *ᵥ a) (a ᵥ* P)

/-- **Sherman–Morrison (right inverse).** If `Y P = 1` and `1 + aᵀ P a ≠ 0`, then
`(Y + a aᵀ) P⁺ = 1`. -/
theorem mul_shermanMorrison {Y P : Matrix n n K} (hYP : Y * P = 1) (a : n → K)
    (hd : 1 + a ⬝ᵥ (P *ᵥ a) ≠ 0) :
    (Y + vecMulVec a a) * shermanMorrison P a = 1 := by
  unfold shermanMorrison
  set c := (1 + a ⬝ᵥ (P *ᵥ a))⁻¹ with hc
  set s := a ⬝ᵥ (P *ᵥ a) with hs
  set U := vecMulVec a (a ᵥ* P) with hU
  have h1 : Y * vecMulVec (P *ᵥ a) (a ᵥ* P) = U := by
    rw [mul_vecMulVec, mulVec_mulVec, hYP, one_mulVec]
  have h2 : vecMulVec a a * P = U := vecMulVec_mul _ _ _
  have h3 : vecMulVec a a * vecMulVec (P *ᵥ a) (a ᵥ* P) = s • U := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hcs : c • U + c • (s • U) = U := by
    rw [smul_smul, ← add_smul, ← mul_one_add, mul_comm, hc, mul_inv_cancel₀ hd, one_smul]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, hYP, Matrix.mul_smul, Matrix.mul_smul,
    h1, h2, h3]
  calc 1 - c • U + (U - c • (s • U)) = 1 + (U - (c • U + c • (s • U))) := by abel
    _ = 1 := by rw [hcs, sub_self, add_zero]

/-- **Sherman–Morrison (left inverse).** If `Y P = 1` and `1 + aᵀ P a ≠ 0`, then
`P⁺ (Y + a aᵀ) = 1`. -/
theorem shermanMorrison_mul {Y P : Matrix n n K} (hYP : Y * P = 1) (a : n → K)
    (hd : 1 + a ⬝ᵥ (P *ᵥ a) ≠ 0) :
    shermanMorrison P a * (Y + vecMulVec a a) = 1 :=
  mul_eq_one_comm.mp (mul_shermanMorrison hYP a hd)

omit [DecidableEq n] in
/-- RLS gain: `P⁺ a = P a / (1 + aᵀ P a)`. -/
theorem shermanMorrison_mulVec (P : Matrix n n K) (a : n → K)
    (hd : 1 + a ⬝ᵥ (P *ᵥ a) ≠ 0) :
    shermanMorrison P a *ᵥ a = (1 + a ⬝ᵥ (P *ᵥ a))⁻¹ • (P *ᵥ a) := by
  unfold shermanMorrison
  rw [sub_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, op_smul_eq_smul,
    smul_smul]
  set s := a ⬝ᵥ (P *ᵥ a)
  calc P *ᵥ a - ((1 + s)⁻¹ * s) • P *ᵥ a = (1 - (1 + s)⁻¹ * s) • P *ᵥ a := by
        rw [sub_smul, one_smul]
    _ = (1 + s)⁻¹ • P *ᵥ a := by
        congr 1
        field_simp
        ring

/-- Recursive least-squares update `x⁺ = x + P⁺ a (β - aᵀ x)`, with `P⁺` the
Sherman–Morrison update of `P`. -/
def rlsUpdate (P : Matrix n n K) (a x : n → K) (β : K) : n → K :=
  x + (β - a ⬝ᵥ x) • (shermanMorrison P a *ᵥ a)

/-- **RLS solves the augmented normal equations (information form).** If `Y P = 1`,
`1 + aᵀ P a ≠ 0` and `Y x = r`, then `(Y + a aᵀ) x⁺ = r + β a`. -/
theorem rlsUpdate_normal {Y P : Matrix n n K} (hYP : Y * P = 1) {a x r : n → K} (β : K)
    (hd : 1 + a ⬝ᵥ (P *ᵥ a) ≠ 0) (hx : Y *ᵥ x = r) :
    (Y + vecMulVec a a) *ᵥ rlsUpdate P a x β = r + β • a := by
  unfold rlsUpdate
  rw [mulVec_add, mulVec_smul, mulVec_mulVec, mul_shermanMorrison hYP a hd, one_mulVec,
    add_mulVec, hx, vecMulVec_mulVec, op_smul_eq_smul, add_assoc, ← add_smul]
  congr 2
  ring

end RLS

/-! ### Recursive least squares on the augmented data set -/

/-- Design matrix after appending one regressor row `aᵀ` below `A`. -/
def augDesign (A : Matrix m n ℝ) (a : n → ℝ) : Matrix (m ⊕ Unit) n ℝ :=
  fromRows A (replicateRow Unit a)

/-- Observation vector after appending one measurement `β` below `b`. -/
def augObs (b : m → ℝ) (β : ℝ) : m ⊕ Unit → ℝ :=
  Sum.elim b fun _ => β

omit [Fintype n] in
/-- Appending the row `aᵀ` adds the rank-one term `a aᵀ` to the Gram matrix. -/
theorem augDesign_gram (A : Matrix m n ℝ) (a : n → ℝ) :
    (augDesign A a)ᵀ * augDesign A a = Aᵀ * A + vecMulVec a a := by
  rw [augDesign, transpose_fromRows, fromCols_mul_fromRows, transpose_replicateRow,
    ← vecMulVec_eq]

omit [Fintype n] in
/-- Appending the row `(aᵀ, β)` adds `β a` to the right-hand side `Aᵀ b`. -/
theorem augDesign_transpose_mulVec (A : Matrix m n ℝ) (a : n → ℝ) (b : m → ℝ) (β : ℝ) :
    (augDesign A a)ᵀ *ᵥ augObs b β = Aᵀ *ᵥ b + β • a := by
  rw [augDesign, transpose_fromRows, augObs, fromCols_mulVec_sumElim, transpose_replicateRow]
  congr 1
  ext i
  simp [mulVec, dotProduct, replicateCol, mul_comm]

section Augmented

variable [DecidableEq n]

private lemma dotProduct_mulVec_nonneg_of_gram_mul {A : Matrix m n ℝ} {P : Matrix n n ℝ}
    (hP : (Aᵀ * A) * P = 1) (a : n → ℝ) : 0 ≤ a ⬝ᵥ (P *ᵥ a) := by
  have ha : (Aᵀ * A) *ᵥ (P *ᵥ a) = a := by rw [mulVec_mulVec, hP, one_mulVec]
  calc 0 ≤ (A *ᵥ (P *ᵥ a)) ⬝ᵥ (A *ᵥ (P *ᵥ a)) :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg _
    _ = a ⬝ᵥ (P *ᵥ a) := by
        rw [mulVec_dotProduct_eq, mulVec_mulVec, dotProduct_comm, ha]

/-- **Recursive least squares.** If `x` is a least-squares solution for `(A, b)` and
`(Aᵀ A) P = 1`, then the RLS update `x⁺ = x + P⁺ a (β - aᵀ x)` is a least-squares solution
for the data set augmented by the row `(aᵀ, β)`. -/
theorem rlsUpdate_isLeastSquares {A : Matrix m n ℝ} {P : Matrix n n ℝ}
    (hP : (Aᵀ * A) * P = 1) {b : m → ℝ} {x : n → ℝ} (hx : IsLeastSquares A b x)
    (a : n → ℝ) (β : ℝ) :
    IsLeastSquares (augDesign A a) (augObs b β) (rlsUpdate P a x β) := by
  rw [isLeastSquares_iff] at hx ⊢
  rw [augDesign_gram, augDesign_transpose_mulVec]
  have hd : 1 + a ⬝ᵥ (P *ᵥ a) ≠ 0 :=
    (by linarith [dotProduct_mulVec_nonneg_of_gram_mul hP a] : (0 : ℝ) < _).ne'
  exact rlsUpdate_normal hP β hd hx

end Augmented

/-! ### Concrete corollary: straight-line fit `y ≈ c₀ + c₁ t` -/

/-- Design matrix of the straight-line model: row `i` is `[1, tᵢ]`. -/
def lineDesign (t : m → ℝ) : Matrix m (Fin 2) ℝ :=
  of fun i => ![1, t i]

/-- Sum of squared residuals of the line `c₀ + c₁ t` on the data `(tᵢ, yᵢ)`. -/
def lineFitCost (t y : m → ℝ) (c₀ c₁ : ℝ) : ℝ :=
  ∑ i, (c₀ + c₁ * t i - y i) ^ 2

/-- The line-fit cost is the residual sum of squares of the design `[1, t]`. -/
theorem lineFitCost_eq_rss (t y : m → ℝ) (c₀ c₁ : ℝ) :
    lineFitCost t y c₀ c₁ = rss (lineDesign t) y ![c₀, c₁] := by
  simp [lineFitCost, rss_eq_sum_sq, lineDesign]

private lemma lineDesign_transpose_mulVec (t : m → ℝ) (v : m → ℝ) :
    (lineDesign t)ᵀ *ᵥ v = ![∑ i, v i, ∑ i, t i * v i] := by
  ext j
  fin_cases j <;> simp [lineDesign, mulVec, dotProduct, mul_comm]

/-- **Line fit, normal equations.** `(c₀, c₁)` minimises `∑ (c₀ + c₁ tᵢ - yᵢ)²` iff
`c₀ N + c₁ ∑ tᵢ = ∑ yᵢ` and `c₀ ∑ tᵢ + c₁ ∑ tᵢ² = ∑ tᵢ yᵢ`. -/
theorem lineFit_isMin_iff (t y : m → ℝ) (c₀ c₁ : ℝ) :
    (∀ d₀ d₁, lineFitCost t y c₀ c₁ ≤ lineFitCost t y d₀ d₁) ↔
      (c₀ * Fintype.card m + c₁ * ∑ i, t i = ∑ i, y i ∧
        c₀ * ∑ i, t i + c₁ * ∑ i, t i ^ 2 = ∑ i, t i * y i) := by
  have hmin : (∀ d₀ d₁, lineFitCost t y c₀ c₁ ≤ lineFitCost t y d₀ d₁) ↔
      IsLeastSquares (lineDesign t) y ![c₀, c₁] := by
    simp only [lineFitCost_eq_rss, IsLeastSquares]
    refine ⟨fun h d => ?_, fun h d₀ d₁ => h _⟩
    have hd : d = ![d 0, d 1] := by ext i; fin_cases i <;> rfl
    rw [hd]; exact h _ _
  rw [hmin, isLeastSquares_iff, ← mulVec_mulVec, lineDesign_transpose_mulVec,
    lineDesign_transpose_mulVec]
  have hAc : lineDesign t *ᵥ ![c₀, c₁] = fun i => c₀ + c₁ * t i := by
    ext i; simp [lineDesign, mulVec, dotProduct, mul_comm]
  rw [hAc]
  simp only [funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e₁ : ∑ i, (c₀ + c₁ * t i) = c₀ * Fintype.card m + c₁ * ∑ i, t i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mul_sum, mul_comm]
  have e₂ : ∑ i, t i * (c₀ + c₁ * t i) = c₀ * ∑ i, t i + c₁ * ∑ i, t i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e₁, e₂]

/-- **Line fit, closed form.** If `D = N ∑ tᵢ² - (∑ tᵢ)² ≠ 0`, the unique minimiser is
`c₀ = (∑ tᵢ² ∑ yᵢ - ∑ tᵢ ∑ tᵢ yᵢ) / D`, `c₁ = (N ∑ tᵢ yᵢ - ∑ tᵢ ∑ yᵢ) / D`. -/
theorem lineFit_isMin_iff_eq (t y : m → ℝ) (c₀ c₁ : ℝ)
    (hD : (Fintype.card m : ℝ) * ∑ i, t i ^ 2 - (∑ i, t i) ^ 2 ≠ 0) :
    (∀ d₀ d₁, lineFitCost t y c₀ c₁ ≤ lineFitCost t y d₀ d₁) ↔
      (c₀ = ((∑ i, t i ^ 2) * ∑ i, y i - (∑ i, t i) * ∑ i, t i * y i) /
          ((Fintype.card m : ℝ) * ∑ i, t i ^ 2 - (∑ i, t i) ^ 2) ∧
        c₁ = ((Fintype.card m : ℝ) * ∑ i, t i * y i - (∑ i, t i) * ∑ i, y i) /
          ((Fintype.card m : ℝ) * ∑ i, t i ^ 2 - (∑ i, t i) ^ 2)) := by
  rw [lineFit_isMin_iff]
  set N : ℝ := (Fintype.card m : ℝ)
  set St := ∑ i, t i
  set Stt := ∑ i, t i ^ 2
  set Sy := ∑ i, y i
  set Sty := ∑ i, t i * y i
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · rw [eq_div_iff hD]; linear_combination Stt * h₁ - St * h₂
    · rw [eq_div_iff hD]; linear_combination N * h₂ - St * h₁
  · rintro ⟨rfl, rfl⟩
    constructor
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring

end ControlsLean.Estimation
