import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Byers–Nash $n=6$: Rank ≤ 4 Real Skew Normal Form and Same-Square Exclusion
# Alternative / Inductive Strategy

This file formalizes the mathematical machinery for the rank ≤ 4 real skew 6×6 normal form lemma:
1. **Geometric Building Blocks**:
   - 2D invariant subspace lemma (`skew_invariant_plane`): any unit eigenvector of `-M²`
     with eigenvalue `lam > 0` generates an orthonormal pair `(u, v)` on which `M` acts as a rotation.
   - Orthogonal complement invariance (`skew_orthogonal_plane_invariant`, `skew_orthogonal_ker_invariant`):
     both 2D invariant planes and kernel vectors have $M$-invariant orthogonal complements.
2. **Orthonormal Basis to Normal Form**:
   - `basisMatrix` and `basisMatrix_transpose_mul_self`: matrix of an orthonormal basis is orthogonal ($Q^\top Q = 1$).
   - `orthonormal_basis_gives_skewWitness`: an adapted orthonormal basis conjugates $K$ into `skewWitness a b`.
3. **Genuine Rank Hypothesis & Dimension Bounds**:
   - `ker_dim_ge_two`: from `K.rank ≤ 4`, rank-nullity proves `2 ≤ finrank ℝ (ker K.mulVecLin)`.
   - `mulVec_eq_zero_of_neg_sq_mulVec_eq_zero`: $\ker(-K^2) = \ker(K)$.
4. **EuclideanSpace Orthonormal Extension**:
   - `coe_orthonormalBasis`: bridge between Mathlib's `OrthonormalBasis` in `EuclideanSpace`
     and the matrix dot product `⬝ᵥ`.
   - `orthonormal_extension_pair`: extension of any orthonormal pair to a full 6D orthonormal basis.
5. **Same-Square Exclusion & Unconditional Gain Comparison**:
   - `rank_four_same_square_exclusion_unconditional` and `rank_four_conjugated_exclusion`:
     unconditional same-square comparator for any conjugated skew witness `Q * skewWitness a b * Qᵀ`.
   - `general_rank_four_exclusion_of_normal_form`: composition of the normal form with same-square exclusion.
-/

namespace Research.SkewRankFourNormalForm

open Matrix

abbrev Mat := Matrix (Fin 6) (Fin 6) ℝ
abbrev Vec := Fin 6 → ℝ
abbrev E6 := EuclideanSpace ℝ (Fin 6)

/-! ## Section 1: Basic Definitions and Invariant Subspaces -/

def frobeniusSquared {n : Type*} [Fintype n] (X : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, (X i j) ^ 2

def lyapunov {n : Type*} [Fintype n] [DecidableEq n] (A X : Matrix n n ℝ) : Matrix n n ℝ :=
  A * X + X * A.transpose

def conjugate {n : Type*} [Fintype n] [DecidableEq n] (Q X : Matrix n n ℝ) : Matrix n n ℝ :=
  Q * X * Q.transpose

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
  ext i j; fin_cases i <;> fin_cases j <;> simp [skewWitness, Matrix.transpose_apply]

theorem symmetricWitness_symmetric (a b : ℝ) :
    (symmetricWitness a b).transpose = symmetricWitness a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symmetricWitness, Matrix.transpose_apply]

theorem same_square (a b : ℝ) :
    symmetricWitness a b * symmetricWitness a b = -(skewWitness a b * skewWitness a b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symmetricWitness, skewWitness, Matrix.mul_apply, Fin.sum_univ_succ]

theorem same_squaredNorm (a b : ℝ) :
    frobeniusSquared (symmetricWitness a b) = frobeniusSquared (skewWitness a b) := by
  simp [frobeniusSquared, symmetricWitness, skewWitness, Fin.sum_univ_succ]

theorem conjugate_transpose (Q X : Mat) :
    (conjugate Q X).transpose = conjugate Q X.transpose := by
  simp [conjugate, Matrix.transpose_mul, Matrix.mul_assoc]

theorem conjugate_symmetric (Q X : Mat) (hX : X.transpose = X) :
    (conjugate Q X).transpose = conjugate Q X := by
  rw [conjugate_transpose, hX]

theorem conjugate_inverse (Q X : Mat) (hQ : Q.transpose * Q = 1) :
    conjugate Q.transpose (conjugate Q X) = X := by
  simp only [conjugate, Matrix.transpose_transpose]
  calc
    Q.transpose * (Q * X * Q.transpose) * Q =
        (Q.transpose * Q) * X * (Q.transpose * Q) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hQ]; simp

theorem frobeniusSquared_eq_trace (X : Mat) :
    frobeniusSquared X = Matrix.trace (X.transpose * X) := by
  simp only [frobeniusSquared, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, sq]
  exact Finset.sum_comm

theorem frobeniusSquared_conjugate (Q X : Mat)
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

theorem lyapunov_conjugate (Q A X : Mat)
    (hQ : Q.transpose * Q = 1) :
    lyapunov (conjugate Q A) (conjugate Q X) = conjugate Q (lyapunov A X) := by
  unfold lyapunov
  rw [conjugate_transpose]
  unfold conjugate
  have hmul (B C : Mat) :
      Q * B * Q.transpose * (Q * C * Q.transpose) = Q * (B * C) * Q.transpose := by
    calc
      _ = Q * B * (Q.transpose * Q) * C * Q.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hmul A X, hmul X A.transpose]
  simp only [Matrix.mul_add, Matrix.add_mul]

theorem lyapunov_frobeniusSquared_conjugate (Q A X : Mat)
    (hQ : Q.transpose * Q = 1) :
    frobeniusSquared (lyapunov (conjugate Q A) (conjugate Q X)) =
      frobeniusSquared (lyapunov A X) := by
  rw [lyapunov_conjugate Q A X hQ, frobeniusSquared_conjugate Q _ hQ]

/-! ## Section 2: Skew-Symmetric Properties and Invariant Subspaces -/

lemma dotProduct_mulVec_comm (A : Mat) (x y : Vec) :
    x ⬝ᵥ (A *ᵥ y) = (A.transpose *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, mulVec, transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j; ring

lemma skew_dotProduct_mulVec_swap (M : Mat) (hM : M.transpose = -M) (u v : Vec) :
    u ⬝ᵥ (M *ᵥ v) = - (v ⬝ᵥ (M *ᵥ u)) := by
  calc
    u ⬝ᵥ (M *ᵥ v) = (M.transpose *ᵥ u) ⬝ᵥ v := dotProduct_mulVec_comm M u v
    _ = (-M *ᵥ u) ⬝ᵥ v := by rw [hM]
    _ = (- (M *ᵥ u)) ⬝ᵥ v := by rw [neg_mulVec]
    _ = - ((M *ᵥ u) ⬝ᵥ v) := neg_dotProduct (M *ᵥ u) v
    _ = - (v ⬝ᵥ (M *ᵥ u)) := by rw [dotProduct_comm]

lemma skew_dotProduct_self_zero (M : Mat) (hM : M.transpose = -M) (u : Vec) :
    u ⬝ᵥ (M *ᵥ u) = 0 := by
  have h1 : u ⬝ᵥ (M *ᵥ u) = - (u ⬝ᵥ (M *ᵥ u)) := skew_dotProduct_mulVec_swap M hM u u
  linarith

lemma skew_neg_sq_symmetric (M : Mat) (hM : M.transpose = -M) :
    (-M * M).transpose = -M * M := by
  simp only [transpose_neg, transpose_mul, hM, neg_mul, mul_neg, neg_neg]

lemma isHermitian_neg_sq (M : Mat) (hM : M.transpose = -M) :
    (-M * M).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact skew_neg_sq_symmetric M hM

/-- **2D Invariant Subspace Lemma**:
Given an eigenvector `u` of `-M²` with strictly positive eigenvalue `lam > 0`,
the vector `v = (1 / √lam) • (M *ᵥ u)` satisfies:
1. `u` and `v` are orthogonal: `u ⬝ᵥ v = 0`.
2. `v` is a unit vector: `v ⬝ᵥ v = 1`.
3. `M *ᵥ u = √lam • v` and `M *ᵥ v = -√lam • u`.
4. `v` is also an eigenvector of `-M²` with the same eigenvalue. -/
theorem skew_invariant_plane
    (M : Mat) (hM : M.transpose = -M)
    (u : Vec) (lam : ℝ)
    (hu_unit : u ⬝ᵥ u = 1) (hu_eig : (-M * M) *ᵥ u = lam • u) (hlam : 0 < lam) :
    let ω := Real.sqrt lam
    let v := (1 / ω) • (M *ᵥ u)
    u ⬝ᵥ v = 0 ∧
    v ⬝ᵥ v = 1 ∧
    M *ᵥ u = ω • v ∧
    M *ᵥ v = -ω • u ∧
    (-M * M) *ᵥ v = lam • v ∧
    ∀ c₁ c₂ : ℝ, M *ᵥ (c₁ • u + c₂ • v) = (-c₂ * ω) • u + (c₁ * ω) • v := by
  intro ω v
  have hω_pos : 0 < ω := Real.sqrt_pos.mpr hlam
  have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
  have hω_sq : ω ^ 2 = lam := Real.sq_sqrt (le_of_lt hlam)
  have h_uv : u ⬝ᵥ v = 0 := by
    dsimp [v]
    rw [dotProduct_smul, skew_dotProduct_self_zero M hM u, smul_eq_mul, mul_zero]
  have h_Mtu_Mu : (M *ᵥ u) ⬝ᵥ (M *ᵥ u) = lam := by
    calc
      (M *ᵥ u) ⬝ᵥ (M *ᵥ u) = (M.transpose *ᵥ (M *ᵥ u)) ⬝ᵥ u := dotProduct_mulVec_comm M (M *ᵥ u) u
      _ = ((-M) *ᵥ (M *ᵥ u)) ⬝ᵥ u := by rw [hM]
      _ = ((-M * M) *ᵥ u) ⬝ᵥ u := by rw [mulVec_mulVec]
      _ = (lam • u) ⬝ᵥ u := by rw [hu_eig]
      _ = lam * (u ⬝ᵥ u) := smul_dotProduct lam u u
      _ = lam := by rw [hu_unit, mul_one]
  have h_vv : v ⬝ᵥ v = 1 := by
    dsimp [v]
    rw [smul_dotProduct, dotProduct_smul, h_Mtu_Mu]
    have : (1 / ω) • ((1 / ω) • lam) = lam / ω ^ 2 := by simp [smul_eq_mul]; ring
    rw [this, hω_sq, div_self (ne_of_gt hlam)]
  have h_Mu : M *ᵥ u = ω • v := by
    dsimp [v]
    rw [smul_smul, mul_one_div_cancel hω_ne, one_smul]
  have h_Mv : M *ᵥ v = -ω • u := by
    dsimp [v]
    rw [mulVec_smul]
    have hM2 : M *ᵥ (M *ᵥ u) = - (lam • u) := by
      calc
        M *ᵥ (M *ᵥ u) = (M * M) *ᵥ u := by rw [← mulVec_mulVec]
        _ = - (- (M * M) *ᵥ u) := by rw [neg_mulVec, neg_neg]
        _ = - ((-M * M) *ᵥ u) := by rw [neg_mul]
        _ = - (lam • u) := by rw [hu_eig]
    rw [hM2]
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    calc
      1 / ω * - (lam * u i) = - ((lam / ω) * u i) := by ring
      _ = - ((ω ^ 2 / ω) * u i) := by rw [hω_sq]
      _ = - (ω * u i) := by rw [sq, mul_div_cancel_right₀ ω hω_ne]
      _ = -ω * u i := by ring
  have h_S_v : (-M * M) *ᵥ v = lam • v := by
    calc
      (-M * M) *ᵥ v = - ((M * M) *ᵥ v) := by rw [neg_mul, neg_mulVec]
      _ = - (M *ᵥ (M *ᵥ v)) := by rw [mulVec_mulVec]
      _ = - (M *ᵥ (-ω • u)) := by rw [h_Mv]
      _ = - ((-ω) • (M *ᵥ u)) := by rw [mulVec_smul]
      _ = - ((-ω) • (ω • v)) := by rw [h_Mu]
      _ = - (((-ω) * ω) • v) := by rw [smul_smul]
      _ = (ω * ω) • v := by
        ext i
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = lam • v := by rw [← sq, hω_sq]
  have h_plane : ∀ c₁ c₂ : ℝ, M *ᵥ (c₁ • u + c₂ • v) = (-c₂ * ω) • u + (c₁ * ω) • v := by
    intro c₁ c₂
    ext i
    simp only [mulVec_add, mulVec_smul, h_Mu, h_Mv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨h_uv, h_vv, h_Mu, h_Mv, h_S_v, h_plane⟩

theorem skew_orthogonal_plane_invariant
    (M : Mat) (hM : M.transpose = -M)
    (u v : Vec) (ω : ℝ)
    (hu : M *ᵥ u = ω • v) (hv : M *ᵥ v = -ω • u)
    (w : Vec) (hwu : w ⬝ᵥ u = 0) (hwv : w ⬝ᵥ v = 0) :
    (M *ᵥ w) ⬝ᵥ u = 0 ∧ (M *ᵥ w) ⬝ᵥ v = 0 := by
  have hu_perp : (M *ᵥ w) ⬝ᵥ u = 0 := by
    calc
      (M *ᵥ w) ⬝ᵥ u = - (w ⬝ᵥ (M *ᵥ u)) := by
        rw [dotProduct_comm, skew_dotProduct_mulVec_swap M hM u w, dotProduct_comm]
      _ = - (w ⬝ᵥ (ω • v)) := by rw [hu]
      _ = - (ω * (w ⬝ᵥ v)) := by rw [dotProduct_smul, smul_eq_mul]
      _ = 0 := by rw [hwv, mul_zero, neg_zero]
  have hv_perp : (M *ᵥ w) ⬝ᵥ v = 0 := by
    calc
      (M *ᵥ w) ⬝ᵥ v = - (w ⬝ᵥ (M *ᵥ v)) := by
        rw [dotProduct_comm, skew_dotProduct_mulVec_swap M hM v w, dotProduct_comm]
      _ = - (w ⬝ᵥ (-ω • u)) := by rw [hv]
      _ = - (-ω * (w ⬝ᵥ u)) := by rw [dotProduct_smul, smul_eq_mul]
      _ = 0 := by rw [hwu, mul_zero, neg_zero]
  exact ⟨hu_perp, hv_perp⟩

theorem skew_orthogonal_ker_invariant
    (M : Mat) (hM : M.transpose = -M)
    (z w : Vec) (hz : M *ᵥ z = 0) (_hwz : w ⬝ᵥ z = 0) :
    (M *ᵥ w) ⬝ᵥ z = 0 := by
  calc
    (M *ᵥ w) ⬝ᵥ z = - (w ⬝ᵥ (M *ᵥ z)) := by
      rw [dotProduct_comm, skew_dotProduct_mulVec_swap M hM z w, dotProduct_comm]
    _ = - (w ⬝ᵥ 0) := by rw [hz]
    _ = 0 := by rw [dotProduct_zero, neg_zero]

lemma skew_range_orthogonal_ker (K : Mat) (hK : K.transpose = -K)
    (z y : Vec) (hz : K *ᵥ z = 0) :
    z ⬝ᵥ (K *ᵥ y) = 0 := by
  calc
    z ⬝ᵥ (K *ᵥ y) = - (y ⬝ᵥ (K *ᵥ z)) := skew_dotProduct_mulVec_swap K hK z y
    _ = - (y ⬝ᵥ 0) := by rw [hz]
    _ = 0 := by simp

/-! ## Section 3: Orthonormal Basis to Normal Form -/

def basisMatrix (q : Fin 6 → Vec) : Mat :=
  Matrix.of (fun i j => q j i)

theorem basisMatrix_col (q : Fin 6 → Vec) (j : Fin 6) :
    Matrix.col (basisMatrix q) j = q j := by
  ext i; simp [basisMatrix, Matrix.col]

theorem basisMatrix_transpose_mul_self (q : Fin 6 → Vec)
    (hortho : ∀ i j : Fin 6, q i ⬝ᵥ q j = if i = j then 1 else 0) :
    (basisMatrix q).transpose * basisMatrix q = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisMatrix, of_apply, one_apply]
  exact hortho i j

theorem orthonormal_basis_gives_skewWitness (K : Mat) (_hK : K.transpose = -K)
    (q : Fin 6 → Vec) (a b : ℝ)
    (hortho : ∀ i j : Fin 6, q i ⬝ᵥ q j = if i = j then 1 else 0)
    (hq0 : K *ᵥ q 0 = -a • q 1)
    (hq1 : K *ᵥ q 1 = a • q 0)
    (hq2 : K *ᵥ q 2 = -b • q 3)
    (hq3 : K *ᵥ q 3 = b • q 2)
    (hq4 : K *ᵥ q 4 = 0)
    (hq5 : K *ᵥ q 5 = 0) :
    let Q := basisMatrix q
    Q.transpose * Q = 1 ∧
    Q.transpose * K * Q = skewWitness a b ∧
    K = conjugate Q (skewWitness a b) := by
  intro Q
  have hQ_ortho : Q.transpose * Q = 1 := basisMatrix_transpose_mul_self q hortho
  have hQT : Q * Q.transpose = 1 := mul_eq_one_comm.mpr hQ_ortho
  have h_entry : ∀ i j : Fin 6, (Q.transpose * K * Q) i j = q i ⬝ᵥ (K *ᵥ q j) := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
    calc
      ∑ k, (∑ l, q i l * K l k) * q j k = ∑ k, ∑ l, q i l * K l k * q j k := by
        simp_rw [Finset.sum_mul]
      _ = ∑ l, ∑ k, q i l * K l k * q j k := Finset.sum_comm
      _ = ∑ l, q i l * (∑ k, K l k * q j k) := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
  have h_norm : Q.transpose * K * Q = skewWitness a b := by
    ext i j
    rw [h_entry]
    fin_cases i <;> fin_cases j <;>
      simp [hq0, hq1, hq2, hq3, hq4, hq5, dotProduct_smul, smul_eq_mul, hortho, skewWitness]
  have h_conj : K = conjugate Q (skewWitness a b) := by
    unfold conjugate
    calc
      K = 1 * K * 1 := by simp
      _ = (Q * Q.transpose) * K * (Q * Q.transpose) := by rw [hQT]
      _ = Q * (Q.transpose * K * Q) * Q.transpose := by simp only [Matrix.mul_assoc]
      _ = Q * skewWitness a b * Q.transpose := by rw [h_norm]
  exact ⟨hQ_ortho, h_norm, h_conj⟩

/-! ## Section 4: Genuine Rank ≤ 4 Hypothesis & Dimension Theorems -/

/-- **Rank-Nullity Dimension Lower Bound for Skew Matrix of Rank ≤ 4**:
By the rank-nullity theorem applied to `K.mulVecLin : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)`,
the dimension of `ker K` is `6 - rank(K) ≥ 6 - 4 = 2`.
This theorem requires NO basis hypotheses and uses Mathlib's genuine `K.rank ≤ 4`. -/
theorem ker_dim_ge_two (K : Mat) (hrank : K.rank ≤ 4) :
    2 ≤ Module.finrank ℝ (LinearMap.ker K.mulVecLin) := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  have h_dim : Module.finrank ℝ (Fin 6 → ℝ) = 6 := by simp
  rw [h_dim] at h_rn
  have h_rk : Module.finrank ℝ (LinearMap.range K.mulVecLin) ≤ 4 := hrank
  omega

lemma inner_eq_dotProduct (u v : E6) : @inner ℝ E6 _ u v = (⇑u : Vec) ⬝ᵥ (⇑v : Vec) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [star, dotProduct_comm]

lemma ker_toEuclideanLin_ge_two (K : Mat) (hrank : K.rank ≤ 4) :
    2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toEuclideanLin K)) := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin K)
  have h_dim : Module.finrank ℝ E6 = 6 := by simp
  rw [h_dim] at h_rn
  have h_rk : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin K)) ≤ 4 := by
    change Module.finrank ℝ (LinearMap.range (Matrix.toLin (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis K)) ≤ 4
    rw [← Matrix.rank_eq_finrank_range_toLin K
      (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis]
    exact hrank
  omega

lemma sum_univ_six_last {M : Type*} [AddCommMonoid M] (f : Fin 6 → M)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h2 : f 2 = 0) (h3 : f 3 = 0) (h4 : f 4 = 0) :
    ∑ i : Fin 6, f i = f 5 := by
  apply Fintype.sum_eq_single (5 : Fin 6)
  intro i hi
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · contradiction

lemma sum_univ_six_fourth {M : Type*} [AddCommMonoid M] (f : Fin 6 → M)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h2 : f 2 = 0) (h3 : f 3 = 0) (h5 : f 5 = 0) :
    ∑ i : Fin 6, f i = f 4 := by
  apply Fintype.sum_eq_single (4 : Fin 6)
  intro i hi
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · contradiction
  · exact h5

/-- Kernel of `-M²` coincides with kernel of `M`:
If `(-M * M) *ᵥ z = 0`, then `M *ᵥ z = 0`. -/
lemma mulVec_eq_zero_of_neg_sq_mulVec_eq_zero (M : Mat) (hM : M.transpose = -M) (z : Vec)
    (hz : (-M * M) *ᵥ z = 0) : M *ᵥ z = 0 := by
  have hdot : (M *ᵥ z) ⬝ᵥ (M *ᵥ z) = 0 := by
    calc
      (M *ᵥ z) ⬝ᵥ (M *ᵥ z) = (M.transpose *ᵥ (M *ᵥ z)) ⬝ᵥ z := dotProduct_mulVec_comm M (M *ᵥ z) z
      _ = ((-M) *ᵥ (M *ᵥ z)) ⬝ᵥ z := by rw [hM]
      _ = ((-M * M) *ᵥ z) ⬝ᵥ z := by rw [mulVec_mulVec]
      _ = 0 ⬝ᵥ z := by rw [hz]
      _ = 0 := zero_dotProduct z
  rw [dotProduct_self_eq_zero] at hdot
  exact hdot

/-! ## Section 5: EuclideanSpace Coercions & Orthonormal Basis Extension -/

/-- Coercion of Mathlib's `OrthonormalBasis` in `EuclideanSpace ℝ (Fin 6)` to
vectors in `Fin 6 → ℝ` satisfies the standard Kronecker delta dot product relation. -/
lemma coe_orthonormalBasis (b : OrthonormalBasis (Fin 6) ℝ E6) (i j : Fin 6) :
    (⇑(b i) : Vec) ⬝ᵥ (⇑(b j) : Vec) = if i = j then 1 else 0 := by
  have h_in : @inner ℝ E6 _ (b i) (b j) = if i = j then 1 else 0 := by
    split_ifs with h
    · subst h
      have h1 := b.orthonormal.1 i
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq, h1, one_pow]
    · exact b.orthonormal.2 h
  have h_dot : @inner ℝ E6 _ (b i) (b j) = (⇑(b i) : Vec) ⬝ᵥ (⇑(b j) : Vec) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star, dotProduct_comm]
  rw [← h_dot, h_in]

/-- Extension of an orthonormal pair `(u, v)` in `E6` to an orthonormal basis of `E6`. -/
theorem orthonormal_extension_pair (u v : E6)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : @inner ℝ E6 _ u v = 0) :
    ∃ b : OrthonormalBasis (Fin 6) ℝ E6, b 0 = u ∧ b 1 = v := by
  let f : Fin 6 → E6 := fun i => if i = 0 then u else if i = 1 then v else 0
  let s : Set (Fin 6) := {0, 1}
  have h_ortho : Orthonormal ℝ (s.domRestrict f) := by
    constructor
    · rintro ⟨i, hi⟩
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      dsimp [f]
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      dsimp [f]
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exfalso; apply hij; ext; rfl
      · exact huv
      · rw [real_inner_comm]; exact huv
      · exfalso; apply hij; ext; rfl
  have hcard : Module.finrank ℝ E6 = Fintype.card (Fin 6) := by simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard h_ortho
  refine ⟨b, hb 0 (by simp [s]), hb 1 (by simp [s])⟩

/-- Extension of an orthonormal 4-tuple in `E6` to a full orthonormal basis of `E6`. -/
theorem orthonormal_extension_four (u0 u1 u2 u3 : E6)
    (h0 : ‖u0‖ = 1) (h1 : ‖u1‖ = 1) (h2 : ‖u2‖ = 1) (h3 : ‖u3‖ = 1)
    (h01 : @inner ℝ E6 _ u0 u1 = 0) (h02 : @inner ℝ E6 _ u0 u2 = 0) (h03 : @inner ℝ E6 _ u0 u3 = 0)
    (h12 : @inner ℝ E6 _ u1 u2 = 0) (h13 : @inner ℝ E6 _ u1 u3 = 0) (h23 : @inner ℝ E6 _ u2 u3 = 0) :
    ∃ b : OrthonormalBasis (Fin 6) ℝ E6, b 0 = u0 ∧ b 1 = u1 ∧ b 2 = u2 ∧ b 3 = u3 := by
  let f : Fin 6 → E6 := fun i =>
    if i = 0 then u0 else if i = 1 then u1 else if i = 2 then u2 else if i = 3 then u3 else 0
  let s : Set (Fin 6) := {0, 1, 2, 3}
  have h_ortho : Orthonormal ℝ (s.domRestrict f) := by
    constructor
    · rintro ⟨i, hi⟩
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      dsimp [f]
      rcases hi with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      dsimp [f]
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
      · exfalso; apply hij; ext; rfl
      · exact h01
      · exact h02
      · exact h03
      · rw [real_inner_comm]; exact h01
      · exfalso; apply hij; ext; rfl
      · exact h12
      · exact h13
      · rw [real_inner_comm]; exact h02
      · rw [real_inner_comm]; exact h12
      · exfalso; apply hij; ext; rfl
      · exact h23
      · rw [real_inner_comm]; exact h03
      · rw [real_inner_comm]; exact h13
      · rw [real_inner_comm]; exact h23
      · exfalso; apply hij; ext; rfl
  have hcard : Module.finrank ℝ E6 = Fintype.card (Fin 6) := by simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard h_ortho
  exact ⟨b, hb 0 (by simp [s]), hb 1 (by simp [s]), hb 2 (by simp [s]), hb 3 (by simp [s])⟩

lemma skew_adapted_complement_block (K : Mat) (hK : K.transpose = -K)
    (b : OrthonormalBasis (Fin 6) ℝ E6) (ω : ℝ)
    (h0 : K *ᵥ (⇑(b 0) : Vec) = ω • (⇑(b 1) : Vec))
    (h1 : K *ᵥ (⇑(b 1) : Vec) = -ω • (⇑(b 0) : Vec))
    (h2 : K *ᵥ (⇑(b 2) : Vec) = 0)
    (h3 : K *ᵥ (⇑(b 3) : Vec) = 0) :
    let β := (⇑(b 5) : Vec) ⬝ᵥ (K *ᵥ (⇑(b 4) : Vec))
    K *ᵥ (⇑(b 4) : Vec) = β • (⇑(b 5) : Vec) ∧
    K *ᵥ (⇑(b 5) : Vec) = -β • (⇑(b 4) : Vec) := by
  intro β
  let x : E6 := Matrix.toEuclideanLin K (b 4)
  have hx_coe : (⇑x : Vec) = K *ᵥ (⇑(b 4) : Vec) := rfl
  have h_in_x (i : Fin 6) : @inner ℝ E6 _ (b i) x = (⇑(b i) : Vec) ⬝ᵥ (K *ᵥ (⇑(b 4) : Vec)) := by
    rw [inner_eq_dotProduct, hx_coe]
  have hx0 : @inner ℝ E6 _ (b 0) x = 0 := by
    rw [h_in_x 0, skew_dotProduct_mulVec_swap K hK, h0, dotProduct_smul, smul_eq_mul]
    have : (⇑(b 4) : Vec) ⬝ᵥ (⇑(b 1) : Vec) = 0 := by
      rw [dotProduct_comm, coe_orthonormalBasis]
      rfl
    rw [this, mul_zero, neg_zero]
  have hx1 : @inner ℝ E6 _ (b 1) x = 0 := by
    rw [h_in_x 1, skew_dotProduct_mulVec_swap K hK, h1, dotProduct_smul, smul_eq_mul]
    have : (⇑(b 4) : Vec) ⬝ᵥ (⇑(b 0) : Vec) = 0 := by
      rw [dotProduct_comm, coe_orthonormalBasis]
      rfl
    rw [this, mul_zero, neg_zero]
  have hx2 : @inner ℝ E6 _ (b 2) x = 0 := by
    rw [h_in_x 2]
    exact skew_range_orthogonal_ker K hK (⇑(b 2)) (⇑(b 4)) h2
  have hx3 : @inner ℝ E6 _ (b 3) x = 0 := by
    rw [h_in_x 3]
    exact skew_range_orthogonal_ker K hK (⇑(b 3)) (⇑(b 4)) h3
  have hx4 : @inner ℝ E6 _ (b 4) x = 0 := by
    rw [h_in_x 4]
    exact skew_dotProduct_self_zero K hK (⇑(b 4))
  have hx5 : @inner ℝ E6 _ (b 5) x = β := by
    rw [h_in_x 5]
  have hx_decomp : x = β • b 5 := by
    have h_rep := b.sum_repr' x
    have h_sum := sum_univ_six_last (fun i => @inner ℝ E6 _ (b i) x • b i)
      (by rw [hx0, zero_smul])
      (by rw [hx1, zero_smul])
      (by rw [hx2, zero_smul])
      (by rw [hx3, zero_smul])
      (by rw [hx4, zero_smul])
    rw [h_sum, hx5] at h_rep
    exact h_rep.symm
  have h_K4 : K *ᵥ (⇑(b 4) : Vec) = β • (⇑(b 5) : Vec) := by
    calc
      K *ᵥ (⇑(b 4) : Vec) = (⇑x : Vec) := hx_coe.symm
      _ = (⇑(β • b 5) : Vec) := by rw [hx_decomp]
      _ = β • (⇑(b 5) : Vec) := rfl

  let y : E6 := Matrix.toEuclideanLin K (b 5)
  have hy_coe : (⇑y : Vec) = K *ᵥ (⇑(b 5) : Vec) := rfl
  have h_in_y (i : Fin 6) : @inner ℝ E6 _ (b i) y = (⇑(b i) : Vec) ⬝ᵥ (K *ᵥ (⇑(b 5) : Vec)) := by
    rw [inner_eq_dotProduct, hy_coe]
  have hy0 : @inner ℝ E6 _ (b 0) y = 0 := by
    rw [h_in_y 0, skew_dotProduct_mulVec_swap K hK, h0, dotProduct_smul, smul_eq_mul]
    have : (⇑(b 5) : Vec) ⬝ᵥ (⇑(b 1) : Vec) = 0 := by
      rw [dotProduct_comm, coe_orthonormalBasis]
      rfl
    rw [this, mul_zero, neg_zero]
  have hy1 : @inner ℝ E6 _ (b 1) y = 0 := by
    rw [h_in_y 1, skew_dotProduct_mulVec_swap K hK, h1, dotProduct_smul, smul_eq_mul]
    have : (⇑(b 5) : Vec) ⬝ᵥ (⇑(b 0) : Vec) = 0 := by
      rw [dotProduct_comm, coe_orthonormalBasis]
      rfl
    rw [this, mul_zero, neg_zero]
  have hy2 : @inner ℝ E6 _ (b 2) y = 0 := by
    rw [h_in_y 2]
    exact skew_range_orthogonal_ker K hK (⇑(b 2)) (⇑(b 5)) h2
  have hy3 : @inner ℝ E6 _ (b 3) y = 0 := by
    rw [h_in_y 3]
    exact skew_range_orthogonal_ker K hK (⇑(b 3)) (⇑(b 5)) h3
  have hy5 : @inner ℝ E6 _ (b 5) y = 0 := by
    rw [h_in_y 5]
    exact skew_dotProduct_self_zero K hK (⇑(b 5))
  have hy4 : @inner ℝ E6 _ (b 4) y = -β := by
    rw [h_in_y 4, skew_dotProduct_mulVec_swap K hK]
  have hy_decomp : y = (-β) • b 4 := by
    have h_rep := b.sum_repr' y
    have h_sum := sum_univ_six_fourth (fun i => @inner ℝ E6 _ (b i) y • b i)
      (by rw [hy0, zero_smul])
      (by rw [hy1, zero_smul])
      (by rw [hy2, zero_smul])
      (by rw [hy3, zero_smul])
      (by rw [hy5, zero_smul])
    rw [h_sum, hy4] at h_rep
    exact h_rep.symm
  have h_K5 : K *ᵥ (⇑(b 5) : Vec) = -β • (⇑(b 4) : Vec) := by
    calc
      K *ᵥ (⇑(b 5) : Vec) = (⇑y : Vec) := hy_coe.symm
      _ = (⇑((-β) • b 4) : Vec) := by rw [hy_decomp]
      _ = (-β) • (⇑(b 4) : Vec) := rfl
      _ = -β • (⇑(b 4) : Vec) := by simp
  exact ⟨h_K4, h_K5⟩

def adaptedIndex : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 0
  | 2 => 5
  | 3 => 4
  | 4 => 2
  | 5 => 3

noncomputable def adaptedBasis (b : OrthonormalBasis (Fin 6) ℝ E6) (i : Fin 6) : Vec :=
  ⇑(b (adaptedIndex i))

lemma adaptedBasis_ortho (b : OrthonormalBasis (Fin 6) ℝ E6) (i j : Fin 6) :
    adaptedBasis b i ⬝ᵥ adaptedBasis b j = if i = j then 1 else 0 := by
  dsimp [adaptedBasis]
  fin_cases i <;> fin_cases j <;> {
    rw [coe_orthonormalBasis]
    rfl
  }




/-! ## Section 6: Same-Square Exclusion & Gain Comparison -/

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

theorem unit_normal_exists (p q : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ p * s - q * c = 0 := by
  by_cases hpq : p ^ 2 + q ^ 2 = 0
  · refine ⟨1, 0, by norm_num, ?_⟩
    have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    simp [hp, hq]
  · have hpos : 0 < p ^ 2 + q ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hpq)
    let r := Real.sqrt (p ^ 2 + q ^ 2)
    have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt (le_of_lt hpos)
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    refine ⟨p / r, q / r, ?_, ?_⟩
    · calc
        (p / r) ^ 2 + (q / r) ^ 2 = (p ^ 2 + q ^ 2) / r ^ 2 := by ring
        _ = r ^ 2 / r ^ 2 := by rw [hr2]
        _ = 1 := div_self (pow_ne_zero 2 hr0)
    · ring

theorem half_angle_exists (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ x ^ 2 - y ^ 2 = c ∧ 2 * x * y = s := by
  by_cases hc : c = -1
  · refine ⟨0, 1, by norm_num, by linarith, ?_⟩
    have hs2 : s ^ 2 = 0 := by rw [hc] at hcs; linarith
    have hs : s = 0 := sq_eq_zero_iff.mp hs2
    linarith
  · have h1c_nonneg : 0 ≤ 1 + c := by
      have h2 : 0 ≤ (1 + c) ^ 2 + s ^ 2 := by positivity
      have h3 : (1 + c) ^ 2 + s ^ 2 = 2 * (1 + c) := by linear_combination hcs
      linarith
    have h1c_pos : 0 < 1 + c := lt_of_le_of_ne h1c_nonneg (by intro h; apply hc; linarith)
    have hx2_nonneg : 0 ≤ (1 + c) / 2 := by linarith
    let x := Real.sqrt ((1 + c) / 2)
    have hx_sq : x ^ 2 = (1 + c) / 2 := Real.sq_sqrt hx2_nonneg
    have hx_pos : 0 < x := Real.sqrt_pos.mpr (by linarith)
    have hx_ne : 2 * x ≠ 0 := by linarith
    let y := s / (2 * x)
    have hy_mul : 2 * x * y = s := mul_div_cancel₀ s hx_ne
    have hy_sq : y ^ 2 = (1 - c) / 2 := by
      have h4x2 : 4 * x ^ 2 * y ^ 2 = s ^ 2 := by
        calc
          4 * x ^ 2 * y ^ 2 = (2 * x * y) ^ 2 := by ring
          _ = s ^ 2 := by rw [hy_mul]
      rw [hx_sq] at h4x2
      have h_eq : (1 + c) * (2 * y ^ 2 - (1 - c)) = 0 := by
        linear_combination h4x2 + hcs
      cases mul_eq_zero.mp h_eq with
      | inl h_zero => exfalso; linarith
      | inr h_y => linarith
    refine ⟨x, y, by linarith, by linarith, hy_mul⟩

theorem signed_svd_angles_exist (b00 b01 b10 b11 : ℝ) :
    ∃ cu su cv sv : ℝ,
      cu ^ 2 + su ^ 2 = 1 ∧
      cv ^ 2 + sv ^ 2 = 1 ∧
      -cu * sv * b00 + cu * cv * b01 - su * sv * b10 + su * cv * b11 = 0 ∧
      -su * cv * b00 - su * sv * b01 + cu * cv * b10 + cu * sv * b11 = 0 := by
  obtain ⟨cp, sp, hcp, heqp⟩ := unit_normal_exists (b00 - b11) (b01 + b10)
  obtain ⟨cm, sm, hcm, heqm⟩ := unit_normal_exists (b00 + b11) (b01 - b10)
  have h2cs : (cp * cm + sp * sm) ^ 2 + (sp * cm - cp * sm) ^ 2 = 1 := by
    calc
      (cp * cm + sp * sm) ^ 2 + (sp * cm - cp * sm) ^ 2 =
          (cp ^ 2 + sp ^ 2) * (cm ^ 2 + sm ^ 2) := by ring
      _ = 1 * 1 := by rw [hcp, hcm]
      _ = 1 := by ring
  obtain ⟨x, y, hxy, hcos2, hsin2⟩ :=
    half_angle_exists (cp * cm + sp * sm) (sp * cm - cp * sm) h2cs
  let cu := x
  let su := y
  let cv := x * cm - y * sm
  let sv := x * sm + y * cm
  have hcv : cv ^ 2 + sv ^ 2 = 1 := by
    dsimp [cv, sv]
    calc
      (x * cm - y * sm) ^ 2 + (x * sm + y * cm) ^ 2 =
          (x ^ 2 + y ^ 2) * (cm ^ 2 + sm ^ 2) := by ring
      _ = 1 * 1 := by rw [hxy, hcm]
      _ = 1 := by ring
  have h_sum_c : cu * cv - su * sv = cp := by
    dsimp [cu, su, cv, sv]
    linear_combination cm * hcos2 - sm * hsin2 + cp * hcm
  have h_sum_s : su * cv + cu * sv = sp := by
    dsimp [cu, su, cv, sv]
    linear_combination sm * hcos2 + cm * hsin2 + sp * hcm
  have h_diff_c : cu * cv + su * sv = cm := by
    dsimp [cu, su, cv, sv]
    linear_combination cm * hxy
  have h_diff_s : su * cv - cu * sv = -sm := by
    dsimp [cu, su, cv, sv]
    linear_combination -sm * hxy
  refine ⟨cu, su, cv, sv, hxy, hcv, ?_, ?_⟩
  · have h1 : -cu * sv * b00 + cu * cv * b01 - su * sv * b10 + su * cv * b11 =
        (1/2) * ((b01 + b10) * (cu * cv - su * sv) - (b00 - b11) * (su * cv + cu * sv)) +
        (1/2) * ((b01 - b10) * (cu * cv + su * sv) - (b00 + b11) * (cu * sv - su * cv)) := by ring
    rw [h1, h_sum_c, h_sum_s, h_diff_c]
    have h_diff_sm : cu * sv - su * cv = sm := by linear_combination -h_diff_s
    rw [h_diff_sm]
    have hp_cancel : (b01 + b10) * cp - (b00 - b11) * sp = 0 := by linear_combination -heqp
    have hm_cancel : (b01 - b10) * cm - (b00 + b11) * sm = 0 := by linear_combination -heqm
    linarith
  · have h2 : -su * cv * b00 - su * sv * b01 + cu * cv * b10 + cu * sv * b11 =
        (1/2) * ((b01 + b10) * (cu * cv - su * sv) - (b00 - b11) * (su * cv + cu * sv)) -
        (1/2) * ((b01 - b10) * (cu * cv + su * sv) - (b00 + b11) * (cu * sv - su * cv)) := by ring
    rw [h2, h_sum_c, h_sum_s, h_diff_c]
    have h_diff_sm : cu * sv - su * cv = sm := by linear_combination -h_diff_s
    rw [h_diff_sm]
    have hp_cancel : (b01 + b10) * cp - (b00 - b11) * sp = 0 := by linear_combination -heqp
    have hm_cancel : (b01 - b10) * cm - (b00 + b11) * sm = 0 := by linear_combination -heqm
    linarith

def blockRot6 (cu su cv sv : ℝ) : Mat :=
  !![cu, -su, 0, 0, 0, 0;
     su,  cu, 0, 0, 0, 0;
     0, 0, cv, -sv, 0, 0;
     0, 0, sv,  cv, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

theorem blockRot6_orthogonal (cu su cv sv : ℝ)
    (hu : cu ^ 2 + su ^ 2 = 1) (hv : cv ^ 2 + sv ^ 2 = 1) :
    (blockRot6 cu su cv sv).transpose * blockRot6 cu su cv sv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [blockRot6, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    linarith

theorem blockRot6_preserves_skewWitness (cu su cv sv a b : ℝ)
    (hu : cu ^ 2 + su ^ 2 = 1) (hv : cv ^ 2 + sv ^ 2 = 1) :
    conjugate (blockRot6 cu su cv sv) (skewWitness a b) = skewWitness a b := by
  have hua : su * a * su + cu * a * cu = a := by linear_combination a * hu
  have hu_neg : -(cu * a * cu) + -(su * a * su) = -a := by linear_combination -a * hu
  have hvb : sv * b * sv + cv * b * cv = b := by linear_combination b * hv
  have hv_neg : -(cv * b * cv) + -(sv * b * sv) = -b := by linear_combination -b * hv
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjugate, blockRot6, skewWitness, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;>
    linarith [hua, hu_neg, hvb, hv_neg]

theorem rank_four_same_square_exclusion_rot (A : Mat) (a b cu su cv sv : ℝ)
    (hu : cu ^ 2 + su ^ 2 = 1) (hv : cv ^ 2 + sv ^ 2 = 1)
    (h03 : (conjugate (blockRot6 cu su cv sv).transpose A) 0 3 = 0)
    (h12 : (conjugate (blockRot6 cu su cv sv).transpose A) 1 2 = 0) :
    ∃ S : Mat, S.transpose = S ∧
      S * S = -(skewWitness a b * skewWitness a b) ∧
      frobeniusSquared S = frobeniusSquared (skewWitness a b) ∧
      frobeniusSquared (lyapunov A (skewWitness a b)) ≤
        frobeniusSquared (lyapunov A S) := by
  let R := blockRot6 cu su cv sv
  have hR : R.transpose * R = 1 := blockRot6_orthogonal cu su cv sv hu hv
  have hRT : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hRT' : R.transpose.transpose * R.transpose = 1 := by simpa using hRT
  refine ⟨conjugate R (symmetricWitness a b),
    conjugate_symmetric R _ (symmetricWitness_symmetric a b),
    ?_, ?_, ?_⟩
  · have hmul : conjugate R (symmetricWitness a b) * conjugate R (symmetricWitness a b) =
        conjugate R (symmetricWitness a b * symmetricWitness a b) := by
      unfold conjugate
      calc
        R * symmetricWitness a b * R.transpose * (R * symmetricWitness a b * R.transpose) =
            R * symmetricWitness a b * (R.transpose * R) * symmetricWitness a b * R.transpose := by
          simp only [Matrix.mul_assoc]
        _ = R * (symmetricWitness a b * symmetricWitness a b) * R.transpose := by
          rw [hR]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hmulK : skewWitness a b * skewWitness a b =
        conjugate R (skewWitness a b * skewWitness a b) := by
      have hKpres := blockRot6_preserves_skewWitness cu su cv sv a b hu hv
      calc
        skewWitness a b * skewWitness a b =
            conjugate R (skewWitness a b) * conjugate R (skewWitness a b) := by
          conv_lhs => rw [← hKpres]
        _ = R * skewWitness a b * (R.transpose * R) * skewWitness a b * R.transpose := by
          unfold conjugate; simp only [Matrix.mul_assoc]
        _ = conjugate R (skewWitness a b * skewWitness a b) := by
          unfold conjugate; rw [hR]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hneg : conjugate R (-(skewWitness a b * skewWitness a b)) =
        -conjugate R (skewWitness a b * skewWitness a b) := by
      unfold conjugate; simp only [Matrix.mul_neg, Matrix.neg_mul]
    rw [hmul, same_square, hneg, ← hmulK]
  · rw [frobeniusSquared_conjugate R _ hR, same_squaredNorm]
  · have hA : A = conjugate R (conjugate R.transpose A) :=
      (conjugate_inverse R.transpose A hRT').symm
    have hK : skewWitness a b = conjugate R (skewWitness a b) :=
      (blockRot6_preserves_skewWitness cu su cv sv a b hu hv).symm
    rw [hA]
    conv_lhs => rw [hK]
    rw [lyapunov_frobeniusSquared_conjugate R (conjugate R.transpose A) _ hR,
        lyapunov_frobeniusSquared_conjugate R (conjugate R.transpose A) _ hR]
    exact gain_comparison (conjugate R.transpose A) a b h03 h12

theorem rank_four_same_square_exclusion_unconditional (A : Mat) (a b : ℝ) :
    ∃ S : Mat, S.transpose = S ∧
      S * S = -(skewWitness a b * skewWitness a b) ∧
      frobeniusSquared S = frobeniusSquared (skewWitness a b) ∧
      frobeniusSquared (lyapunov A (skewWitness a b)) ≤
        frobeniusSquared (lyapunov A S) := by
  obtain ⟨cu, su, cv, sv, hu, hv, h01, h10⟩ :=
    signed_svd_angles_exist (A 0 2) (A 0 3) (A 1 2) (A 1 3)
  have h03 : (conjugate (blockRot6 cu su cv sv).transpose A) 0 3 = 0 := by
    simp [conjugate, blockRot6, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    linarith
  have h12 : (conjugate (blockRot6 cu su cv sv).transpose A) 1 2 = 0 := by
    simp [conjugate, blockRot6, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    linarith
  exact rank_four_same_square_exclusion_rot A a b cu su cv sv hu hv h03 h12

/-- **Unconditional Rank-4 Conjugated Exclusion**:
For any orthogonal matrix `Q` (`Qᵀ * Q = 1`) and any `a, b : ℝ`, the conjugated
witness `K = conjugate Q (skewWitness a b)` admits a same-square symmetric comparator `S`
such that `‖L_A(K)‖_F^2 ≤ ‖L_A(S)‖_F^2`. -/
theorem rank_four_conjugated_exclusion (Q A : Mat) (a b : ℝ)
    (hQ : Q.transpose * Q = 1) :
    ∃ S : Mat, S.transpose = S ∧
      S * S = -(conjugate Q (skewWitness a b) * conjugate Q (skewWitness a b)) ∧
      frobeniusSquared S = frobeniusSquared (conjugate Q (skewWitness a b)) ∧
      frobeniusSquared (lyapunov A (conjugate Q (skewWitness a b))) ≤
        frobeniusSquared (lyapunov A S) := by
  have hQT : Q * Q.transpose = 1 := mul_eq_one_comm.mpr hQ
  have hQT' : Q.transpose.transpose * Q.transpose = 1 := by simpa using hQT
  obtain ⟨S0, hS0_sym, hS0_sq, hS0_norm, hS0_gain⟩ :=
    rank_four_same_square_exclusion_unconditional (conjugate Q.transpose A) a b
  refine ⟨conjugate Q S0, conjugate_symmetric Q S0 hS0_sym, ?_, ?_, ?_⟩
  · have hmulS : conjugate Q S0 * conjugate Q S0 = conjugate Q (S0 * S0) := by
      unfold conjugate
      calc
        Q * S0 * Q.transpose * (Q * S0 * Q.transpose) =
            Q * S0 * (Q.transpose * Q) * S0 * Q.transpose := by simp only [Matrix.mul_assoc]
        _ = Q * (S0 * S0) * Q.transpose := by rw [hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hmulK : conjugate Q (skewWitness a b) * conjugate Q (skewWitness a b) =
        conjugate Q (skewWitness a b * skewWitness a b) := by
      unfold conjugate
      calc
        Q * skewWitness a b * Q.transpose * (Q * skewWitness a b * Q.transpose) =
            Q * skewWitness a b * (Q.transpose * Q) * skewWitness a b * Q.transpose := by
          simp only [Matrix.mul_assoc]
        _ = Q * (skewWitness a b * skewWitness a b) * Q.transpose := by
          rw [hQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [hmulS, hS0_sq, hmulK]
    unfold conjugate
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  · rw [frobeniusSquared_conjugate Q S0 hQ,
        frobeniusSquared_conjugate Q _ hQ,
        hS0_norm]
  · have hA : A = conjugate Q (conjugate Q.transpose A) :=
      (conjugate_inverse Q.transpose A hQT').symm
    rw [hA,
        lyapunov_frobeniusSquared_conjugate Q (conjugate Q.transpose A) _ hQ,
        lyapunov_frobeniusSquared_conjugate Q (conjugate Q.transpose A) _ hQ]
    exact hS0_gain

/-! ## Section 7: Master Theorems and Composition -/

/-- The zero matrix trivially admits the skew normal form with `Q = 1` and `a = b = 0`. -/
theorem skew_zero_normal_form :
    ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ (0 : Mat) = conjugate Q (skewWitness a b) := by
  refine ⟨1, 0, 0, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjugate, skewWitness]

/-- **Normal Form Theorem from an Adapted Orthonormal Basis**:
Given a skew-symmetric matrix `K` and an adapted orthonormal basis `q`
(where `K` acts as rotation by `a` on `(q 0, q 1)`, rotation by `b` on `(q 2, q 3)`,
and annihilates `q 4` and `q 5`), the matrix `Q = basisMatrix q` is orthogonal and
conjugates `K` to `skewWitness a b`. -/
theorem skew_rank_four_normal_form_of_adapted_basis (K : Mat) (hK : K.transpose = -K)
    (q : Fin 6 → Vec) (a b : ℝ)
    (hortho : ∀ i j : Fin 6, q i ⬝ᵥ q j = if i = j then 1 else 0)
    (hq0 : K *ᵥ q 0 = -a • q 1) (hq1 : K *ᵥ q 1 = a • q 0)
    (hq2 : K *ᵥ q 2 = -b • q 3) (hq3 : K *ᵥ q 3 = b • q 2)
    (hq4 : K *ᵥ q 4 = 0) (hq5 : K *ᵥ q 5 = 0) :
    ∃ (Q : Mat) (a' b' : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a' b') :=
  ⟨basisMatrix q, a, b, (orthonormal_basis_gives_skewWitness K hK q a b hortho hq0 hq1 hq2 hq3 hq4 hq5).1,
   (orthonormal_basis_gives_skewWitness K hK q a b hortho hq0 hq1 hq2 hq3 hq4 hq5).2.2⟩

/-- **Hypothesis-Free Rank ≤ 4 Real Skew Normal Form**:
For ANY real skew-symmetric 6×6 matrix `K` with rank ≤ 4, there exists an orthogonal matrix `Q`
and real numbers `a, b` such that `K = conjugate Q (skewWitness a b)`.
This theorem requires NO basis hypotheses and uses Mathlib's genuine `K.rank ≤ 4`. -/
theorem skew_rank_le_four_normal_form (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) :
    ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b) := by
  by_cases hK0 : K = 0
  · subst hK0
    exact skew_zero_normal_form
  · have hA : (-K * K).IsHermitian := isHermitian_neg_sq K hK
    let b_eig := hA.eigenvectorBasis
    have h_ex_nonzero : ∃ j : Fin 6, Matrix.toEuclideanLin K (b_eig j) ≠ 0 := by
      by_contra! h_all_zero
      have h_lin_zero : Matrix.toEuclideanLin K = 0 := by
        apply b_eig.toBasis.ext
        intro j
        simp [h_all_zero j]
      have h_K_zero : K = 0 := by
        have : Matrix.toEuclideanLin K = Matrix.toEuclideanLin 0 := by rw [h_lin_zero, map_zero]
        exact Matrix.toEuclideanLin.injective this
      exact hK0 h_K_zero
    obtain ⟨j, hj_ne⟩ := h_ex_nonzero
    let u_e6 := b_eig j
    let u_vec : Vec := ⇑u_e6
    have hu_unit : u_vec ⬝ᵥ u_vec = 1 := by
      have := coe_orthonormalBasis b_eig j j
      simp only [if_true] at this
      exact this
    have hu_eig : (-K * K) *ᵥ u_vec = (hA.eigenvalues j) • u_vec := by
      exact Matrix.IsHermitian.mulVec_eigenvectorBasis hA j
    have h_Ku_ne : K *ᵥ u_vec ≠ 0 := by
      intro h_zero
      apply hj_ne
      ext i
      exact congr_fun h_zero i
    have h_Ku_dot : (K *ᵥ u_vec) ⬝ᵥ (K *ᵥ u_vec) = hA.eigenvalues j := by
      calc
        (K *ᵥ u_vec) ⬝ᵥ (K *ᵥ u_vec) = (K.transpose *ᵥ (K *ᵥ u_vec)) ⬝ᵥ u_vec :=
          dotProduct_mulVec_comm K (K *ᵥ u_vec) u_vec
        _ = ((-K) *ᵥ (K *ᵥ u_vec)) ⬝ᵥ u_vec := by rw [hK]
        _ = ((-K * K) *ᵥ u_vec) ⬝ᵥ u_vec := by rw [mulVec_mulVec]
        _ = ((hA.eigenvalues j) • u_vec) ⬝ᵥ u_vec := by rw [hu_eig]
        _ = hA.eigenvalues j * (u_vec ⬝ᵥ u_vec) := smul_dotProduct (hA.eigenvalues j) u_vec u_vec
        _ = hA.eigenvalues j := by rw [hu_unit, mul_one]
    have hlam_pos : 0 < hA.eigenvalues j := by
      rw [← h_Ku_dot]
      have h_nonneg : 0 ≤ (K *ᵥ u_vec) ⬝ᵥ (K *ᵥ u_vec) := by
        simp only [dotProduct]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have h_ne_zero : (K *ᵥ u_vec) ⬝ᵥ (K *ᵥ u_vec) ≠ 0 := by
        intro h
        rw [dotProduct_self_eq_zero] at h
        exact h_Ku_ne h
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    let ω := Real.sqrt (hA.eigenvalues j)
    have hω_pos : 0 < ω := Real.sqrt_pos.mpr hlam_pos
    let v_e6 : E6 := (1 / ω) • Matrix.toEuclideanLin K u_e6
    let v_vec : Vec := ⇑v_e6
    obtain ⟨h_uv, h_vv, h_Ku, h_Kv, -, -⟩ :=
      skew_invariant_plane K hK u_vec (hA.eigenvalues j) hu_unit hu_eig hlam_pos
    have hu_norm : ‖u_e6‖ = 1 := b_eig.norm_eq_one j
    have hv_norm : ‖v_e6‖ = 1 := by
      have h_sq : ‖v_e6‖ ^ 2 = 1 := by
        calc
          ‖v_e6‖ ^ 2 = @inner ℝ E6 _ v_e6 v_e6 := (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) v_e6).symm
          _ = v_vec ⬝ᵥ v_vec := inner_eq_dotProduct v_e6 v_e6
          _ = 1 := h_vv
      have h_nonneg : 0 ≤ ‖v_e6‖ := norm_nonneg _
      nlinarith
    have huv_inner : @inner ℝ E6 _ u_e6 v_e6 = 0 := by
      calc
        @inner ℝ E6 _ u_e6 v_e6 = u_vec ⬝ᵥ v_vec := inner_eq_dotProduct u_e6 v_e6
        _ = 0 := h_uv

    let N := LinearMap.ker (Matrix.toEuclideanLin K)
    have hN_dim : 2 ≤ Module.finrank ℝ N := ker_toEuclideanLin_ge_two K hrank
    let bN := stdOrthonormalBasis ℝ N
    let i0 : Fin (Module.finrank ℝ N) := ⟨0, by omega⟩
    let i1 : Fin (Module.finrank ℝ N) := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h
      have hval : (0 : ℕ) = 1 := congr_arg Fin.val h
      omega
    let z0 : E6 := (bN i0).val
    let z1 : E6 := (bN i1).val
    have hz0_ker : K *ᵥ (⇑z0 : Vec) = 0 := by
      calc
        K *ᵥ (⇑z0 : Vec) = (⇑(Matrix.toEuclideanLin K z0) : Vec) := rfl
        _ = (⇑(0 : E6) : Vec) := by rw [(bN i0).property]
        _ = 0 := rfl
    have hz1_ker : K *ᵥ (⇑z1 : Vec) = 0 := by
      calc
        K *ᵥ (⇑z1 : Vec) = (⇑(Matrix.toEuclideanLin K z1) : Vec) := rfl
        _ = (⇑(0 : E6) : Vec) := by rw [(bN i1).property]
        _ = 0 := rfl
    have hz0_norm : ‖z0‖ = 1 := by
      have : ‖z0‖ = ‖bN i0‖ := Submodule.norm_coe (bN i0)
      rw [this, bN.norm_eq_one]
    have hz1_norm : ‖z1‖ = 1 := by
      have : ‖z1‖ = ‖bN i1‖ := Submodule.norm_coe (bN i1)
      rw [this, bN.norm_eq_one]
    have hz01_inner : @inner ℝ E6 _ z0 z1 = 0 := by
      have : @inner ℝ E6 _ z0 z1 = @inner ℝ N _ (bN i0) (bN i1) :=
        (Submodule.coe_inner N (bN i0) (bN i1)).symm
      rw [this, bN.inner_eq_zero hi01]

    have h_Ku' : K *ᵥ u_vec = ω • v_vec := h_Ku
    have h_Kv' : K *ᵥ v_vec = -ω • u_vec := h_Kv
    have hu_range : u_vec = K *ᵥ ((- (1 / ω)) • v_vec) := by
      have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
      rw [mulVec_smul]
      change u_vec = (- (1 / ω)) • (K *ᵥ v_vec)
      rw [h_Kv', smul_smul]
      have : - (1 / ω) * -ω = 1 := by
        calc
          - (1 / ω) * -ω = (1 / ω) * ω := by ring
          _ = 1 := one_div_mul_cancel hω_ne
      rw [this, one_smul]
    have hv_range : v_vec = K *ᵥ ((1 / ω) • u_vec) := by
      rw [mulVec_smul]
      rfl

    have huz0 : @inner ℝ E6 _ u_e6 z0 = 0 := by
      calc
        @inner ℝ E6 _ u_e6 z0 = u_vec ⬝ᵥ (⇑z0 : Vec) := inner_eq_dotProduct u_e6 z0
        _ = (⇑z0 : Vec) ⬝ᵥ u_vec := dotProduct_comm _ _
        _ = (⇑z0 : Vec) ⬝ᵥ (K *ᵥ ((- (1 / ω)) • v_vec)) := by rw [hu_range]
        _ = 0 := skew_range_orthogonal_ker K hK (⇑z0) ((- (1 / ω)) • v_vec) hz0_ker
    have hvz0 : @inner ℝ E6 _ v_e6 z0 = 0 := by
      calc
        @inner ℝ E6 _ v_e6 z0 = v_vec ⬝ᵥ (⇑z0 : Vec) := inner_eq_dotProduct v_e6 z0
        _ = (⇑z0 : Vec) ⬝ᵥ v_vec := dotProduct_comm _ _
        _ = (⇑z0 : Vec) ⬝ᵥ (K *ᵥ ((1 / ω) • u_vec)) := by rw [hv_range]
        _ = 0 := skew_range_orthogonal_ker K hK (⇑z0) ((1 / ω) • u_vec) hz0_ker
    have huz1 : @inner ℝ E6 _ u_e6 z1 = 0 := by
      calc
        @inner ℝ E6 _ u_e6 z1 = u_vec ⬝ᵥ (⇑z1 : Vec) := inner_eq_dotProduct u_e6 z1
        _ = (⇑z1 : Vec) ⬝ᵥ u_vec := dotProduct_comm _ _
        _ = (⇑z1 : Vec) ⬝ᵥ (K *ᵥ ((- (1 / ω)) • v_vec)) := by rw [hu_range]
        _ = 0 := skew_range_orthogonal_ker K hK (⇑z1) ((- (1 / ω)) • v_vec) hz1_ker
    have hvz1 : @inner ℝ E6 _ v_e6 z1 = 0 := by
      calc
        @inner ℝ E6 _ v_e6 z1 = v_vec ⬝ᵥ (⇑z1 : Vec) := inner_eq_dotProduct v_e6 z1
        _ = (⇑z1 : Vec) ⬝ᵥ v_vec := dotProduct_comm _ _
        _ = (⇑z1 : Vec) ⬝ᵥ (K *ᵥ ((1 / ω) • u_vec)) := by rw [hv_range]
        _ = 0 := skew_range_orthogonal_ker K hK (⇑z1) ((1 / ω) • u_vec) hz1_ker

    obtain ⟨b, hb0, hb1, hb2, hb3⟩ :=
      orthonormal_extension_four u_e6 v_e6 z0 z1
        hu_norm hv_norm hz0_norm hz1_norm
        huv_inner huz0 huz1 hvz0 hvz1 hz01_inner
    have hb0_act : K *ᵥ (⇑(b 0) : Vec) = ω • (⇑(b 1) : Vec) := by
      rw [hb0, hb1]
      exact h_Ku
    have hb1_act : K *ᵥ (⇑(b 1) : Vec) = -ω • (⇑(b 0) : Vec) := by
      rw [hb0, hb1]
      exact h_Kv
    have hb2_act : K *ᵥ (⇑(b 2) : Vec) = 0 := by
      rw [hb2]
      exact hz0_ker
    have hb3_act : K *ᵥ (⇑(b 3) : Vec) = 0 := by
      rw [hb3]
      exact hz1_ker

    obtain ⟨h_K4, h_K5⟩ :=
      skew_adapted_complement_block K hK b ω hb0_act hb1_act hb2_act hb3_act
    let β := (⇑(b 5) : Vec) ⬝ᵥ (K *ᵥ (⇑(b 4) : Vec))
    let q := adaptedBasis b
    have hortho : ∀ i j : Fin 6, q i ⬝ᵥ q j = if i = j then 1 else 0 :=
      adaptedBasis_ortho b
    have hq0 : K *ᵥ q 0 = -ω • q 1 := by
      change K *ᵥ (⇑(b 1) : Vec) = -ω • (⇑(b 0) : Vec)
      exact hb1_act
    have hq1 : K *ᵥ q 1 = ω • q 0 := by
      change K *ᵥ (⇑(b 0) : Vec) = ω • (⇑(b 1) : Vec)
      exact hb0_act
    have hq2 : K *ᵥ q 2 = -β • q 3 := by
      change K *ᵥ (⇑(b 5) : Vec) = -β • (⇑(b 4) : Vec)
      exact h_K5
    have hq3 : K *ᵥ q 3 = β • q 2 := by
      change K *ᵥ (⇑(b 4) : Vec) = β • (⇑(b 5) : Vec)
      exact h_K4
    have hq4 : K *ᵥ q 4 = 0 := by
      change K *ᵥ (⇑(b 2) : Vec) = 0
      exact hb2_act
    have hq5 : K *ᵥ q 5 = 0 := by
      change K *ᵥ (⇑(b 3) : Vec) = 0
      exact hb3_act
    exact skew_rank_four_normal_form_of_adapted_basis K hK q ω β hortho hq0 hq1 hq2 hq3 hq4 hq5

/-- **General Rank-4 Same-Square Exclusion Composer**:
Any real skew-symmetric matrix `K` that admits an orthogonal conjugation to `skewWitness a b`
is dominated by a same-square symmetric comparator `S` (`Sᵀ = S`, `S² = -K²`, `‖S‖_F² = ‖K‖_F²`)
for any dynamics matrix `A`. -/
theorem general_rank_four_exclusion_of_normal_form (K : Mat)
    (h_nf : ∃ (Q : Mat) (a b : ℝ), Q.transpose * Q = 1 ∧ K = conjugate Q (skewWitness a b))
    (A : Mat) :
    ∃ S : Mat, S.transpose = S ∧
      S * S = -(K * K) ∧
      frobeniusSquared S = frobeniusSquared K ∧
      frobeniusSquared (lyapunov A K) ≤ frobeniusSquared (lyapunov A S) := by
  obtain ⟨Q, a, b, hQ, hK⟩ := h_nf
  obtain ⟨S, hS_sym, hS_sq, hS_norm, hS_gain⟩ := rank_four_conjugated_exclusion Q A a b hQ
  rw [← hK] at hS_sq hS_norm hS_gain
  exact ⟨S, hS_sym, hS_sq, hS_norm, hS_gain⟩

/-- **Hypothesis-Free Rank ≤ 4 Same-Square Exclusion**:
Every real skew-symmetric 6×6 matrix `K` of rank ≤ 4 is dominated in Lyapunov gain
by a same-square symmetric comparator `S` for any dynamics matrix `A`.
This corollary is completely unconditional and closes the Byers-Nash n=6 rank ≤ 4 gap. -/
theorem skew_rank_le_four_same_square_exclusion (K : Mat) (hK : K.transpose = -K) (hrank : K.rank ≤ 4) (A : Mat) :
    ∃ S : Mat, S.transpose = S ∧
      S * S = -(K * K) ∧
      frobeniusSquared S = frobeniusSquared K ∧
      frobeniusSquared (lyapunov A K) ≤ frobeniusSquared (lyapunov A S) :=
  general_rank_four_exclusion_of_normal_form K (skew_rank_le_four_normal_form K hK hrank) A

#print axioms ker_dim_ge_two
#print axioms ker_toEuclideanLin_ge_two
#print axioms skew_invariant_plane
#print axioms skew_orthogonal_plane_invariant
#print axioms orthonormal_basis_gives_skewWitness
#print axioms coe_orthonormalBasis
#print axioms orthonormal_extension_pair
#print axioms orthonormal_extension_four
#print axioms skew_adapted_complement_block
#print axioms adaptedBasis_ortho
#print axioms rank_four_same_square_exclusion_unconditional
#print axioms rank_four_conjugated_exclusion
#print axioms skew_zero_normal_form
#print axioms skew_rank_four_normal_form_of_adapted_basis
#print axioms skew_rank_le_four_normal_form
#print axioms general_rank_four_exclusion_of_normal_form
#print axioms skew_rank_le_four_same_square_exclusion

end Research.SkewRankFourNormalForm

