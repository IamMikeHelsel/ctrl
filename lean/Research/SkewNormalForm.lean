import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Byers–Nash $n=6$: Normal Form Lemma for Real Skew Matrices of Rank ≤ 4
# and the Unconditional Same-Square Exclusion Theorem
-/

namespace Research.SkewNormalForm

open Matrix

abbrev Mat := Matrix (Fin 6) (Fin 6) ℝ
abbrev Vec := Fin 6 → ℝ

/-! ## Section 1: Basic Definitions and Operators -/

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

/-! ## Section 2: Step A.1 — 2D Invariant Subspace Lemma -/

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

/-- **2D Invariant Subspace Lemma** (Step A.1):
For any real skew-symmetric matrix `M` (`Mᵀ = -M`), `-M²` is symmetric positive semidefinite.
Given a unit eigenvector `u` of `-M²` with strictly positive eigenvalue `lam > 0`,
the vector `v = (1 / √lam) • (M *ᵥ u)` satisfies:
1. `u` and `v` are orthogonal: `u ⬝ᵥ v = 0`.
2. `v` is a unit vector: `v ⬝ᵥ v = 1`.
3. `M *ᵥ u = √lam • v` and `M *ᵥ v = -√lam • u`.
4. `v` is also an eigenvector of `-M²` with the same eigenvalue: `(-M * M) *ᵥ v = lam • v`.
5. The 2D plane `span(u, v)` is `M`-invariant, with `M` acting as a rotation `√lam • J`. -/
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

/-! ## Section 3: Step A.2 — Orthogonal Invariant Complement -/

/-- **Orthogonal Invariant Complement for a 2D Invariant Plane** (Step A.2):
If `span(u, v)` is invariant under a skew matrix `M` (`M u = ω v` and `M v = -ω u`),
then any vector `w` orthogonal to both `u` and `v` has its image `M w` also
orthogonal to both `u` and `v`. -/
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

/-- **Orthogonal Invariant Complement for Kernel Vectors** (Step A.2):
If `z ∈ ker M` (`M *ᵥ z = 0`), then any vector `w` orthogonal to `z`
has `M *ᵥ w` also orthogonal to `z`. -/
theorem skew_orthogonal_ker_invariant
    (M : Mat) (hM : M.transpose = -M)
    (z w : Vec) (hz : M *ᵥ z = 0) (_hwz : w ⬝ᵥ z = 0) :
    (M *ᵥ w) ⬝ᵥ z = 0 := by
  calc
    (M *ᵥ w) ⬝ᵥ z = - (w ⬝ᵥ (M *ᵥ z)) := by
      rw [dotProduct_comm, skew_dotProduct_mulVec_swap M hM z w, dotProduct_comm]
    _ = - (w ⬝ᵥ 0) := by rw [hz]
    _ = 0 := by rw [dotProduct_zero, neg_zero]

/-! ## Section 4: Orthonormal Basis to Normal Form Lemma -/

def basisMatrix (q : Fin 6 → Vec) : Mat :=
  Matrix.of (fun i j => q j i)

theorem basisMatrix_col (q : Fin 6 → Vec) (j : Fin 6) :
    Matrix.col (basisMatrix q) j = q j := by
  ext i
  simp [basisMatrix, Matrix.col]

theorem basisMatrix_transpose_mul_self (q : Fin 6 → Vec)
    (hortho : ∀ i j : Fin 6, q i ⬝ᵥ q j = if i = j then 1 else 0) :
    (basisMatrix q).transpose * basisMatrix q = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, basisMatrix, of_apply, one_apply]
  exact hortho i j

/-- **Orthonormal Basis to Normal Form Theorem**:
Given an orthonormal basis $(q_0, \dots, q_5)$ of $\mathbb{R}^6$ adapted to the invariant
planes and kernel of a skew matrix $K$, the matrix $Q$ whose columns are $q_j$ is orthogonal
($Q^\top Q = 1$) and conjugates $K$ into the block diagonal form `skewWitness a b`. -/
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

/-! ## Section 5: Unconditional Rank-4 Same-Square Exclusion on `skewWitness a b` -/

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
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockRot6, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    linarith

theorem blockRot6_preserves_skewWitness (cu su cv sv a b : ℝ)
    (hu : cu ^ 2 + su ^ 2 = 1) (hv : cv ^ 2 + sv ^ 2 = 1) :
    conjugate (blockRot6 cu su cv sv) (skewWitness a b) = skewWitness a b := by
  have hua : su * a * su + cu * a * cu = a := by linear_combination a * hu
  have hu_neg : -(cu * a * cu) + -(su * a * su) = -a := by linear_combination -a * hu
  have hvb : sv * b * sv + cv * b * cv = b := by linear_combination b * hv
  have hv_neg : -(cv * b * cv) + -(sv * b * sv) = -b := by linear_combination -b * hv
  ext i j
  fin_cases i <;> fin_cases j <;>
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
      unfold conjugate
      simp only [Matrix.mul_neg, Matrix.neg_mul]
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

#print axioms skew_invariant_plane
#print axioms skew_orthogonal_plane_invariant
#print axioms skew_orthogonal_ker_invariant
#print axioms orthonormal_basis_gives_skewWitness
#print axioms rank_four_same_square_exclusion_unconditional
#print axioms rank_four_conjugated_exclusion

end Research.SkewNormalForm
