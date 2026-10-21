module
public import LeanControls.OrthogonalLyapunov
public import LeanControls.RankFourCore
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# Same-Square Exclusion and Rank-2 / Rank-4 Lyapunov Comparison

This file formalizes, completely axiom-clean (zero `sorry`):
1. **Formula (1)** (`same_square_energy_diff`):
   `E_A(S) - E_A(K) = 2 * tr((A*S)^2 + (A*K)^2)` for any `n × n` real matrices
   where `S` is symmetric, `K` is skew-symmetric, and `S^2 = -K^2`.
2. **2×2 Block Lemmas & Unconditional Signed SVD**:
   - `R(c, s)` is symmetric, `R(c, s)^2 = -J_2^2` (given `c^2 + s^2 = 1`), `J_2^T = -J_2`.
   - Diagonal block identity (`block2_diag_trace_identity`):
     `tr((B R)^2 + (B J)^2) = (tr(B R))^2 + (tr(B J))^2 ≥ 0`.
   - Off-diagonal cross-term cancellation (`block2_cross_trace_cancel`):
     for any diagonal 2×2 matrix `D` and arbitrary 2×2 matrix `N`,
     `tr(D X N X + D J N J) = 0`.
   - Unconditional `SO(2) × SO(2)` signed SVD (`signed_svd_2x2_exists`):
     for EVERY 2×2 real matrix `B`, there exist `U, V ∈ SO(2)` preserving `J_2`
     such that `U^T B V` is diagonal (`(U^T B V) 0 1 = 0` and `(U^T B V) 1 0 = 0`).
3. **Rank-2 Exclusion** (`rank_two_dim2_comparison`, `rank_two_gain_difference`,
   `rank_two_gain_comparison`, `rank_two_conjugated_exclusion`):
   every rank-≤2 skew witness in `Fin 2` or `Fin 6` (in any orthogonal basis, with arbitrary
   couplings to the remaining 4 coordinates) is dominated by a same-square symmetric witness.
4. **Unconditional Rank-4 Same-Square Exclusion in `Fin 6`**
   (`rank_four_same_square_exclusion_unconditional` and `rank_four_conjugated_exclusion`):
   for EVERY `A : Matrix (Fin 6) (Fin 6) ℝ`, every orthogonal `Q`, and every `a, b : ℝ`,
   there exists a symmetric same-square witness `S` (`S^T = S`, `S^2 = -(Q K Q^T)^2`,
   `‖S‖_F^2 = ‖Q K Q^T‖_F^2`) such that `E_A(Q K Q^T) ≤ E_A(S)`, where `K = skewWitness a b`.
5. **Coupled-Pair Converse in General Dimension `n`** (`coupled_elimination_converse`):
   for any invertible skew-symmetric `K` (`K * Kinv = 1`, `Kinv * K = 1`), skew-symmetric `Y`,
   and symmetric `B` satisfying `(K Y) B - B (Y K) = 2 K^3 - Y^2 K - K Y^2`, the matrix
   `A2 = (B + Y) Kinv` satisfies `A2 K + K A2^T = 2 Y` and `A2^T Y + Y A2 = 2 K`.
-/
@[expose] public section
noncomputable section
namespace LeanControls.SameSquareExclusion
open Matrix
open LeanControls.DiagonalLyapunov (frobeniusSquared)
open LeanControls.OrthogonalLyapunov (lyapunov conjugate frobeniusSquared_eq_trace)
open LeanControls.RankFourCore (Mat skewWitness symmetricWitness skewWitness_skew
  symmetricWitness_symmetric same_square same_squaredNorm gain_difference gain_comparison
  conjugated_comparison)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Section 1: Formula (1) in arbitrary dimension `n` -/

omit [DecidableEq n] in
/-- Formula (1): For `S` symmetric, `K` skew-symmetric, and `S^2 = -K^2`,
`E_A(S) - E_A(K) = 2 * tr((A*S)^2 + (A*K)^2)`. -/
theorem same_square_energy_diff (A S K : Matrix n n ℝ)
    (hS : S.transpose = S) (hK : K.transpose = -K)
    (hsq : S * S = -(K * K)) :
    frobeniusSquared (lyapunov A S) - frobeniusSquared (lyapunov A K) =
      2 * Matrix.trace ((A * S) * (A * S) + (A * K) * (A * K)) := by
  rw [frobeniusSquared_eq_trace, frobeniusSquared_eq_trace]
  unfold lyapunov
  have hL_S : (A * S + S * A.transpose).transpose = S * A.transpose + A * S := by
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hS, add_comm]
  have hL_K : (A * K + K * A.transpose).transpose = -(K * A.transpose + A * K) := by
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hK, Matrix.neg_mul, Matrix.mul_neg,
      ← neg_add, add_comm]
  rw [hL_S, hL_K]
  have hexpS : (S * A.transpose + A * S) * (A * S + S * A.transpose) =
      (S * A.transpose) * (S * A.transpose) + S * A.transpose * A * S +
      (A * S) * (A * S) + A * (S * S) * A.transpose := by noncomm_ring
  have hexpK : -(K * A.transpose + A * K) * (A * K + K * A.transpose) =
      -((K * A.transpose) * (K * A.transpose)) - K * A.transpose * A * K -
      (A * K) * (A * K) + A * (-(K * K)) * A.transpose := by noncomm_ring
  rw [hexpS, hexpK, ← hsq]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg]
  have hcycS : Matrix.trace ((S * A.transpose) * (S * A.transpose)) =
      Matrix.trace ((A * S) * (A * S)) := by
    have h1 : Matrix.trace ((A * S) * (A * S)) =
        Matrix.trace (((A * S) * (A * S)).transpose) :=
      (Matrix.trace_transpose _).symm
    have h2 : ((A * S) * (A * S)).transpose = (S * A.transpose) * (S * A.transpose) := by
      simp [Matrix.transpose_mul, hS, Matrix.mul_assoc]
    rw [h1, h2]
  have hcycK : Matrix.trace ((K * A.transpose) * (K * A.transpose)) =
      Matrix.trace ((A * K) * (A * K)) := by
    have h1 : Matrix.trace ((A * K) * (A * K)) =
        Matrix.trace (((A * K) * (A * K)).transpose) :=
      (Matrix.trace_transpose _).symm
    have h2 : ((A * K) * (A * K)).transpose = (K * A.transpose) * (K * A.transpose) := by
      simp [Matrix.transpose_mul, hK, Matrix.mul_assoc]
    rw [h1, h2]
  have hcancel : Matrix.trace (S * A.transpose * A * S) =
      -Matrix.trace (K * A.transpose * A * K) := by
    rw [Matrix.trace_mul_cycle (S * A.transpose) A S,
        Matrix.trace_mul_cycle (K * A.transpose) A K]
    have hSS : S * (S * A.transpose) * A = (S * S) * (A.transpose * A) := by
      simp only [Matrix.mul_assoc]
    have hKK : K * (K * A.transpose) * A = (K * K) * (A.transpose * A) := by
      simp only [Matrix.mul_assoc]
    rw [hSS, hKK, hsq, Matrix.neg_mul, Matrix.trace_neg]
  linarith

omit [DecidableEq n] in
/-- Corollary of Formula (1): whenever `tr((A*S)^2 + (A*K)^2) ≥ 0`, the same-square
symmetric comparator `S` has at least the Lyapunov energy of `K`. -/
theorem same_square_comparison_of_trace_nonneg (A S K : Matrix n n ℝ)
    (hS : S.transpose = S) (hK : K.transpose = -K)
    (hsq : S * S = -(K * K))
    (htr : 0 ≤ Matrix.trace ((A * S) * (A * S) + (A * K) * (A * K))) :
    frobeniusSquared (lyapunov A K) ≤ frobeniusSquared (lyapunov A S) := by
  have h := same_square_energy_diff A S K hS hK hsq
  linarith

/-! ## Section 2: 2×2 Block Lemmas, Reflections, and Unconditional Signed SVD -/

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def J2 : Mat2 := !![0, 1; -1, 0]

def X2 : Mat2 := !![0, 1; 1, 0]

def refl2 (c s : ℝ) : Mat2 := !![c, s; s, -c]

def rot2 (c s : ℝ) : Mat2 := !![c, -s; s, c]

theorem J2_skew : J2.transpose = -J2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2, Matrix.transpose_apply]

theorem X2_symm : X2.transpose = X2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X2, Matrix.transpose_apply]

theorem refl2_symm (c s : ℝ) : (refl2 c s).transpose = refl2 c s := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [refl2, Matrix.transpose_apply]

theorem refl2_sq (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    refl2 c s * refl2 c s = -(J2 * J2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [refl2, J2, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    linarith

/-- Diagonal 2×2 block identity in Formula (2):
For any 2×2 matrix `B` and unit reflection `R = refl2 c s` (`c^2 + s^2 = 1`),
`tr((B R)^2 + (B J)^2) = (tr(B R))^2 + (tr(B J))^2`. -/
theorem block2_diag_trace_identity (B : Mat2) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    Matrix.trace ((B * refl2 c s) * (B * refl2 c s) + (B * J2) * (B * J2)) =
      (Matrix.trace (B * refl2 c s)) ^ 2 + (Matrix.trace (B * J2)) ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, refl2, J2]
  linear_combination 2 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) * hcs

theorem block2_diag_trace_nonneg (B : Mat2) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    0 ≤ Matrix.trace ((B * refl2 c s) * (B * refl2 c s) + (B * J2) * (B * J2)) := by
  rw [block2_diag_trace_identity B c s hcs]
  positivity

/-- Rank-two comparison in dimension 2: for any `B : Mat2` and unit reflection `refl2 c s`,
`E_B(refl2 c s) - E_B(J2) = 2 * ((tr(B * refl2 c s))^2 + (tr(B * J2))^2) ≥ 0`. -/
theorem rank_two_dim2_comparison (B : Mat2) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    frobeniusSquared (lyapunov B (refl2 c s)) - frobeniusSquared (lyapunov B J2) =
      2 * ((Matrix.trace (B * refl2 c s)) ^ 2 + (Matrix.trace (B * J2)) ^ 2) := by
  rw [same_square_energy_diff B (refl2 c s) J2 (refl2_symm c s) J2_skew (refl2_sq c s hcs),
      block2_diag_trace_identity B c s hcs]

/-- Off-diagonal cross-term cancellation in Formula (2):
For any 2×2 matrix `D` whose off-diagonal entries vanish (`D 0 1 = 0`, `D 1 0 = 0`)
and ANY 2×2 matrix `N`, `tr(D * X2 * N * X2 + D * J2 * N * J2) = 0`. -/
theorem block2_cross_trace_cancel (D N : Mat2) (h01 : D 0 1 = 0) (h10 : D 1 0 = 0) :
    Matrix.trace (D * X2 * N * X2 + D * J2 * N * J2) = 0 := by
  simp [Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, X2, J2, h01, h10]

/-- Every `SO(2)` rotation preserves `J2`: `rot2 c sᵀ * J2 * rot2 c s = J2`. -/
theorem rot2_preserves_J2 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (rot2 c s).transpose * J2 * rot2 c s = J2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot2, J2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    linarith

theorem rot2_orthogonal (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (rot2 c s).transpose * rot2 c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    linarith

/-- Explicit 2×2 signed SVD off-diagonal entries: for `U = rot2 cu su` and `V = rot2 cv sv`,
the off-diagonal entries of `U^T * B * V` vanish whenever the linear equations hold. -/
theorem signed_svd_2x2_offdiag (B : Mat2) (cu su cv sv : ℝ)
    (h01 : -cu * sv * B 0 0 + cu * cv * B 0 1 - su * sv * B 1 0 + su * cv * B 1 1 = 0)
    (h10 : -su * cv * B 0 0 - su * sv * B 0 1 + cu * cv * B 1 0 + cu * sv * B 1 1 = 0) :
    ((rot2 cu su).transpose * B * rot2 cv sv) 0 1 = 0 ∧
      ((rot2 cu su).transpose * B * rot2 cv sv) 1 0 = 0 := by
  constructor
  · simp [rot2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    linarith
  · simp [rot2, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
    linarith

/-- For any `(p, q) ∈ ℝ²`, there exists a unit vector `(c, s)` (`c^2 + s^2 = 1`)
such that `p * s - q * c = 0`. -/
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

/-- Algebraic half-angle existence: for any `(c, s)` on the unit circle (`c^2 + s^2 = 1`),
there exist `(x, y)` on the unit circle (`x^2 + y^2 = 1`) with `x^2 - y^2 = c` and `2 x y = s`. -/
theorem half_angle_exists (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ x ^ 2 - y ^ 2 = c ∧ 2 * x * y = s := by
  by_cases hc : c = -1
  · refine ⟨0, 1, by norm_num, by linarith, ?_⟩
    have hs2 : s ^ 2 = 0 := by
      rw [hc] at hcs
      linarith
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

/-- Unconditional existence of `SO(2) × SO(2)` signed-SVD angles for any four real entries. -/
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
        (1/2) * ((b01 - b10) * (cu * cv + su * sv) + (b00 + b11) * (su * cv - cu * sv)) := by ring
    rw [h1, h_sum_c, h_sum_s, h_diff_c, h_diff_s]
    linear_combination -(1/2) * heqp - (1/2) * heqm
  · have h2 : -su * cv * b00 - su * sv * b01 + cu * cv * b10 + cu * sv * b11 =
        (1/2) * ((b01 + b10) * (cu * cv - su * sv) - (b00 - b11) * (su * cv + cu * sv)) -
        (1/2) * ((b01 - b10) * (cu * cv + su * sv) + (b00 + b11) * (su * cv - cu * sv)) := by ring
    rw [h2, h_sum_c, h_sum_s, h_diff_c, h_diff_s]
    linear_combination -(1/2) * heqp + (1/2) * heqm

/-- Unconditional 2×2 Signed SVD Theorem: for every `B : Mat2`, there exist `SO(2)` rotations
`rot2 cu su` and `rot2 cv sv` (preserving `J2`) such that `(rot2 cu su)ᵀ * B * rot2 cv sv`
is diagonal. -/
theorem signed_svd_2x2_exists (B : Mat2) :
    ∃ cu su cv sv : ℝ,
      cu ^ 2 + su ^ 2 = 1 ∧
      cv ^ 2 + sv ^ 2 = 1 ∧
      ((rot2 cu su).transpose * B * rot2 cv sv) 0 1 = 0 ∧
      ((rot2 cu su).transpose * B * rot2 cv sv) 1 0 = 0 := by
  obtain ⟨cu, su, cv, sv, hu, hv, h01, h10⟩ :=
    signed_svd_angles_exist (B 0 0) (B 0 1) (B 1 0) (B 1 1)
  obtain ⟨hd01, hd10⟩ := signed_svd_2x2_offdiag B cu su cv sv h01 h10
  exact ⟨cu, su, cv, sv, hu, hv, hd01, hd10⟩

/-! ## Section 3: Rank-2 Exclusion in `Fin 6` (with arbitrary coupling to remaining 4 coordinates) -/

/-- Rank-2 witness in `Fin 6` is the special case `b = 0` of `skewWitness a 0`.
No off-diagonal condition on `A` is needed when `b = 0`! -/
theorem rank_two_gain_difference (A : Mat) (a : ℝ) :
    frobeniusSquared (lyapunov A (symmetricWitness a 0)) -
      frobeniusSquared (lyapunov A (skewWitness a 0)) =
    4 * a ^ 2 * ((A 0 1) ^ 2 + (A 1 0) ^ 2) := by
  simp [frobeniusSquared, lyapunov, symmetricWitness, skewWitness,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_succ]
  ring

theorem rank_two_gain_comparison (A : Mat) (a : ℝ) :
    frobeniusSquared (lyapunov A (skewWitness a 0)) ≤
      frobeniusSquared (lyapunov A (symmetricWitness a 0)) := by
  have h := rank_two_gain_difference A a
  have hnonneg : 0 ≤ 4 * a ^ 2 * ((A 0 1) ^ 2 + (A 1 0) ^ 2) := by positivity
  linarith

/-- Unconditional Rank-2 Exclusion in `Fin 6`: for any orthogonal `Q`, any `A : Mat`,
and any rank-≤2 skew witness `conjugate Q (skewWitness a 0)`, there exists a symmetric
comparator `S` with the same Frobenius norm and at least its Lyapunov amplification. -/
theorem rank_two_conjugated_exclusion (Q A : Mat) (a : ℝ)
    (hQ : Q.transpose * Q = 1) :
    ∃ S : Mat, S.transpose = S ∧
      frobeniusSquared S = frobeniusSquared (conjugate Q (skewWitness a 0)) ∧
      frobeniusSquared (lyapunov A (conjugate Q (skewWitness a 0))) ≤
        frobeniusSquared (lyapunov A S) := by
  have hQT : Q * Q.transpose = 1 := mul_eq_one_comm.mpr hQ
  refine ⟨conjugate Q (symmetricWitness a 0),
     LeanControls.OrthogonalLyapunov.conjugate_symmetric Q _ (symmetricWitness_symmetric a 0), ?_, ?_⟩
  · rw [LeanControls.OrthogonalLyapunov.frobeniusSquared_conjugate Q _ hQ,
        LeanControls.OrthogonalLyapunov.frobeniusSquared_conjugate Q _ hQ,
        same_squaredNorm]
  · have hA : A = conjugate Q (conjugate Q.transpose A) := by
      have hQT' : Q.transpose.transpose * Q.transpose = 1 := by simpa using hQT
      exact (LeanControls.OrthogonalLyapunov.conjugate_inverse Q.transpose A hQT').symm
    rw [hA,
        LeanControls.OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate Q (conjugate Q.transpose A) _ hQ,
        LeanControls.OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate Q (conjugate Q.transpose A) _ hQ]
    exact rank_two_gain_comparison (conjugate Q.transpose A) a

/-! ## Section 4: Unconditional Rank-4 Same-Square Exclusion in `Fin 6` -/

/-- Embed two `SO(2)` rotations `(cu, su)` and `(cv, sv)` into the first two 2×2 blocks of `Mat`. -/
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

/-- Crucially, `blockRot6` preserves `skewWitness a b`! -/
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

/-- Rank-4 Same-Square Exclusion in `Fin 6` given `SO(2) × SO(2)` signed-SVD angles. -/
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
    LeanControls.OrthogonalLyapunov.conjugate_symmetric R _ (symmetricWitness_symmetric a b),
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
  · rw [LeanControls.OrthogonalLyapunov.frobeniusSquared_conjugate R _ hR, same_squaredNorm]
  · have hA : A = conjugate R (conjugate R.transpose A) :=
      (LeanControls.OrthogonalLyapunov.conjugate_inverse R.transpose A hRT').symm
    have hK : skewWitness a b = conjugate R (skewWitness a b) :=
      (blockRot6_preserves_skewWitness cu su cv sv a b hu hv).symm
    rw [hA]
    conv_lhs => rw [hK]
    rw [LeanControls.OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate R (conjugate R.transpose A) _ hR,
        LeanControls.OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate R (conjugate R.transpose A) _ hR]
    exact gain_comparison (conjugate R.transpose A) a b h03 h12

/-- **Unconditional Rank-4 Same-Square Exclusion in `Fin 6`**:
For EVERY 6×6 real matrix `A` and every `a, b : ℝ`, there exists a symmetric matrix `S`
with `S^2 = -(skewWitness a b)^2` and `‖S‖_F^2 = ‖skewWitness a b‖_F^2` such that
`‖L_A(skewWitness a b)‖_F^2 ≤ ‖L_A(S)‖_F^2`. -/
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

/-- **Unconditional Rank-4 Exclusion in Any Orthogonal Basis of `Fin 6`**:
For EVERY 6×6 real matrix `A`, every orthogonal `Q` (`Qᵀ * Q = 1`), and every `a, b : ℝ`,
the rank-≤4 skew witness `K = conjugate Q (skewWitness a b)` admits a same-square symmetric
witness `S` (`Sᵀ = S`, `S^2 = -K^2`, `‖S‖_F^2 = ‖K‖_F^2`) such that `E_A(K) ≤ E_A(S)`. -/
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
  refine ⟨conjugate Q S0,
    LeanControls.OrthogonalLyapunov.conjugate_symmetric Q S0 hS0_sym, ?_, ?_, ?_⟩
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
  · rw [LeanControls.OrthogonalLyapunov.frobeniusSquared_conjugate Q S0 hQ,
        LeanControls.OrthogonalLyapunov.frobeniusSquared_conjugate Q _ hQ,
        hS0_norm]
  · have hA : A = conjugate Q (conjugate Q.transpose A) :=
      (LeanControls.OrthogonalLyapunov.conjugate_inverse Q.transpose A hQT').symm
    rw [hA,
        LeanControls.OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate Q (conjugate Q.transpose A) _ hQ,
        LeanControls.OrthogonalLyapunov.lyapunov_frobeniusSquared_conjugate Q (conjugate Q.transpose A) _ hQ]
    exact hS0_gain

/-! ## Section 5: Coupled-Pair Converse in General Dimension `n` -/

/-- Division-free coupled-pair converse: Suppose `K, Y` are skew-symmetric, `K * Kinv = 1`,
`Kinv * K = 1`, and `B` is symmetric (`Bᵀ = B`) satisfying the linear elimination equation
`(K * Y) * B - B * (Y * K) = 2 • K^3 - Y^2 * K - K * Y^2`.
Define `A2 = (B + Y) * Kinv` (which is `2 • A`). Then:
1. `A2 * K + K * A2ᵀ = 2 • Y`
2. `A2ᵀ * Y + Y * A2 = 2 • K`. -/
theorem coupled_elimination_converse (K Kinv Y B : Matrix n n ℝ)
    (hK : K.transpose = -K) (hY : Y.transpose = -Y) (hB : B.transpose = B)
    (hK_right : K * Kinv = 1) (hK_left : Kinv * K = 1)
    (helim : (K * Y) * B - B * (Y * K) = K ^ 3 + K ^ 3 - Y ^ 2 * K - K * Y ^ 2) :
    let A2 := (B + Y) * Kinv
    A2 * K + K * A2.transpose = Y + Y ∧
      A2.transpose * Y + Y * A2 = K + K := by
  intro A2
  have hKinv_skew : Kinv.transpose = -Kinv := by
    calc
      Kinv.transpose = Kinv.transpose * (K * Kinv) := by rw [hK_right, Matrix.mul_one]
      _ = Kinv.transpose * (-K.transpose) * Kinv := by rw [hK, neg_neg, Matrix.mul_assoc]
      _ = -(K * Kinv).transpose * Kinv := by simp [Matrix.transpose_mul]
      _ = -Kinv := by rw [hK_right]; simp
  have hA2K : A2 * K = B + Y := by
    dsimp [A2]
    rw [Matrix.mul_assoc, hK_left, Matrix.mul_one]
  have hKA2T : K * A2.transpose = Y - B := by
    dsimp [A2]
    rw [Matrix.transpose_mul, Matrix.transpose_add, hB, hY, hKinv_skew]
    calc
      K * (-Kinv * (B + -Y)) = -(K * Kinv) * (B - Y) := by noncomm_ring
      _ = Y - B := by rw [hK_right]; noncomm_ring
  constructor
  · rw [hA2K, hKA2T]; abel
  · have hmul : K * (A2.transpose * Y + Y * A2) * K = K * (K + K) * K := by
      calc
        K * (A2.transpose * Y + Y * A2) * K =
            (K * A2.transpose) * Y * K + K * Y * (A2 * K) := by noncomm_ring
        _ = (Y - B) * Y * K + K * Y * (B + Y) := by rw [hKA2T, hA2K]
        _ = ((K * Y) * B - B * (Y * K)) + Y ^ 2 * K + K * Y ^ 2 := by noncomm_ring
        _ = (K ^ 3 + K ^ 3 - Y ^ 2 * K - K * Y ^ 2) + Y ^ 2 * K + K * Y ^ 2 := by rw [helim]
        _ = K * (K + K) * K := by noncomm_ring
    calc
      A2.transpose * Y + Y * A2 = Kinv * (K * (A2.transpose * Y + Y * A2) * K) * Kinv := by
        calc
          A2.transpose * Y + Y * A2 = 1 * (A2.transpose * Y + Y * A2) * 1 := by simp
          _ = (Kinv * K) * (A2.transpose * Y + Y * A2) * (K * Kinv) := by rw [hK_left, hK_right]
          _ = Kinv * (K * (A2.transpose * Y + Y * A2) * K) * Kinv := by simp only [Matrix.mul_assoc]
      _ = Kinv * (K * (K + K) * K) * Kinv := by rw [hmul]
      _ = (Kinv * K) * (K + K) * (K * Kinv) := by simp only [Matrix.mul_assoc]
      _ = K + K := by rw [hK_left, hK_right]; simp

#print axioms same_square_energy_diff
#print axioms same_square_comparison_of_trace_nonneg
#print axioms block2_diag_trace_identity
#print axioms block2_diag_trace_nonneg
#print axioms rank_two_dim2_comparison
#print axioms block2_cross_trace_cancel
#print axioms rot2_preserves_J2
#print axioms signed_svd_2x2_offdiag
#print axioms unit_normal_exists
#print axioms half_angle_exists
#print axioms signed_svd_angles_exist
#print axioms signed_svd_2x2_exists
#print axioms rank_two_gain_difference
#print axioms rank_two_gain_comparison
#print axioms rank_two_conjugated_exclusion
#print axioms blockRot6_orthogonal
#print axioms blockRot6_preserves_skewWitness
#print axioms rank_four_same_square_exclusion_rot
#print axioms rank_four_same_square_exclusion_unconditional
#print axioms rank_four_conjugated_exclusion
#print axioms coupled_elimination_converse

end LeanControls.SameSquareExclusion
