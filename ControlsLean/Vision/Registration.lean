/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination

/-!
# Point-cloud registration: optimal translation and the Kabsch / Umeyama reduction

Given point pairs `(p i, q i)`, `i : ι` (a nonempty finite index type, `N := card ι`), in real
inner product spaces, ICP / Kabsch / Umeyama registration minimises
`J(f, t) = ∑ i, ‖f (p i) + t - q i‖²` over a linear map `f` (a rotation in practice) and a
translation `t`. Write `p̄, q̄` for the centroids.

* **Optimal translation** (`registrationCost_eq`): for every linear `f` and every `t`,
  `J(f, t) = J(f, t⋆) + N ‖t - t⋆‖²` with `t⋆ = q̄ - f p̄`. Hence `t⋆` is a minimiser
  (`registrationCost_optimalTranslation_le`) and the unique one
  (`registrationCost_eq_optimal_iff`). At `t⋆` the cost is the cost of the centred clouds
  `p' i = p i - p̄`, `q' i = q i - q̄` (`registrationCost_optimalTranslation`).
* **Rotation step** (`sum_norm_sub_sq_isometry`): for a linear isometry `R`,
  `∑ ‖R p i - q i‖² = ∑ ‖p i‖² + ∑ ‖q i‖² - 2 ∑ ⟪R p i, q i⟫`, so minimising the cost over
  isometries is equivalent to maximising the correlation `∑ ⟪R p i, q i⟫`
  (`sum_norm_sub_sq_le_iff`). Combined with the translation step: an isometry maximising the
  centred correlation, together with its optimal translation, minimises `J` over all
  isometries and translations (`registrationCost_le_of_crossCorrelation_max`).
* **Matrix form** (`sum_mulVec_dotProduct_eq_trace`): `∑ (R pᵢ) ⬝ (qᵢ) = tr (Rᵀ H)` with the
  cross-covariance `H = ∑ qᵢ pᵢᵀ` (over any commutative ring), and the same with the
  Euclidean inner product on `EuclideanSpace ℝ (Fin d)` (`sum_inner_toEuclideanLin_eq_trace`).
* **Planar case**: `a cos θ + b sin θ ≤ √(a² + b²)` (`mul_cos_add_mul_sin_le`), with equality
  at `θ = arg (a + b i)` (the `atan2 (b, a)` angle; `mul_cos_add_mul_sin_arg`), and for
  `(a, b) ≠ 0` only at angles congruent to it modulo `2π` (`angle_eq_arg_of_eq_sqrt`). For the
  rotation `rot2 θ`, the correlation is `a cos θ + b sin θ` with `a = H₀₀ + H₁₁`,
  `b = H₁₀ - H₀₁` (`sum_rot2_dotProduct`), so `θ = arg (a + b i)` minimises the planar cost
  `∑ ‖rot2 θ pᵢ - qᵢ‖²` (squared Euclidean norm written as a dot product) over all angles
  (`rot2Cost_arg_le`).
-/

open Finset Matrix
open scoped InnerProductSpace

namespace ControlsLean.Vision

section Translation

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The centroid `(1 / N) ∑ i, p i` of a finite family of points. -/
noncomputable def centroid (p : ι → E) : E := (Fintype.card ι : ℝ)⁻¹ • ∑ i, p i

theorem sum_eq_card_smul_centroid [Nonempty ι] (p : ι → E) :
    ∑ i, p i = (Fintype.card ι : ℝ) • centroid p := by
  rw [centroid, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

/-- Centred points sum to zero. -/
theorem sum_sub_centroid [Nonempty ι] (p : ι → E) : ∑ i, (p i - centroid p) = 0 := by
  rw [sum_sub_distrib, sum_const, card_univ, sum_eq_card_smul_centroid, Nat.cast_smul_eq_nsmul,
    sub_self]

/-- The registration cost `J(f, t) = ∑ i, ‖f (p i) + t - q i‖²`. -/
noncomputable def registrationCost (f : E →ₗ[ℝ] F) (p : ι → E) (q : ι → F) (t : F) : ℝ :=
  ∑ i, ‖f (p i) + t - q i‖ ^ 2

/-- The optimal translation `t⋆ = q̄ - f p̄`. -/
noncomputable def optimalTranslation (f : E →ₗ[ℝ] F) (p : ι → E) (q : ι → F) : F :=
  centroid q - f (centroid p)

/-- At the optimal translation, each residual is the residual of the centred points. -/
theorem residual_optimalTranslation (f : E →ₗ[ℝ] F) (p : ι → E) (q : ι → F) (i : ι) :
    f (p i) + optimalTranslation f p q - q i = f (p i - centroid p) - (q i - centroid q) := by
  rw [optimalTranslation, map_sub]; abel

/-- At the optimal translation the residuals sum to zero. -/
theorem sum_residual_optimalTranslation [Nonempty ι] (f : E →ₗ[ℝ] F) (p : ι → E)
    (q : ι → F) : ∑ i, (f (p i) + optimalTranslation f p q - q i) = 0 := by
  simp_rw [residual_optimalTranslation]
  rw [sum_sub_distrib, ← map_sum, sum_sub_centroid, sum_sub_centroid, map_zero, sub_zero]

/-- The cost at the optimal translation equals the cost of the centred point clouds. -/
theorem registrationCost_optimalTranslation (f : E →ₗ[ℝ] F) (p : ι → E) (q : ι → F) :
    registrationCost f p q (optimalTranslation f p q) =
      ∑ i, ‖f (p i - centroid p) - (q i - centroid q)‖ ^ 2 := by
  simp_rw [registrationCost, residual_optimalTranslation]

/-- **Exact decomposition of the registration cost**:
`J(f, t) = J(f, t⋆) + N ‖t - t⋆‖²` with `t⋆ = q̄ - f p̄`. -/
theorem registrationCost_eq [Nonempty ι] (f : E →ₗ[ℝ] F) (p : ι → E) (q : ι → F) (t : F) :
    registrationCost f p q t = registrationCost f p q (optimalTranslation f p q) +
      Fintype.card ι * ‖t - optimalTranslation f p q‖ ^ 2 := by
  have h : ∀ i, f (p i) + t - q i =
      (f (p i) + optimalTranslation f p q - q i) + (t - optimalTranslation f p q) :=
    fun i => by abel
  have hs := sum_residual_optimalTranslation f p q
  rw [registrationCost]
  simp_rw [h, norm_add_sq_real, sum_add_distrib, ← mul_sum, ← sum_inner, hs, inner_zero_left,
    mul_zero, add_zero, sum_const, card_univ, nsmul_eq_mul]
  rfl

/-- **Optimality of the centroid translation**: `J(f, t⋆) ≤ J(f, t)` for every `t`. -/
theorem registrationCost_optimalTranslation_le [Nonempty ι] (f : E →ₗ[ℝ] F) (p : ι → E)
    (q : ι → F) (t : F) :
    registrationCost f p q (optimalTranslation f p q) ≤ registrationCost f p q t := by
  rw [registrationCost_eq f p q t]
  have : (0 : ℝ) ≤ Fintype.card ι * ‖t - optimalTranslation f p q‖ ^ 2 := by positivity
  linarith

/-- **Uniqueness of the optimal translation**: `J(f, t) = J(f, t⋆)` iff `t = t⋆`. -/
theorem registrationCost_eq_optimal_iff [Nonempty ι] (f : E →ₗ[ℝ] F) (p : ι → E)
    (q : ι → F) (t : F) :
    registrationCost f p q t = registrationCost f p q (optimalTranslation f p q) ↔
      t = optimalTranslation f p q := by
  rw [registrationCost_eq f p q t, add_eq_left, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero, sub_eq_zero, Nat.cast_eq_zero]
  simp [Fintype.card_ne_zero]

end Translation

section Rotation

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The correlation `∑ i, ⟪R (p i), q i⟫` maximised in the rotation step. -/
noncomputable def crossCorrelation (R : E →ₗᵢ[ℝ] F) (p : ι → E) (q : ι → F) : ℝ :=
  ∑ i, ⟪R (p i), q i⟫_ℝ

/-- For an isometry, `∑ ‖R pᵢ - qᵢ‖² = ∑ ‖pᵢ‖² + ∑ ‖qᵢ‖² - 2 ∑ ⟪R pᵢ, qᵢ⟫`. -/
theorem sum_norm_sub_sq_isometry (R : E →ₗᵢ[ℝ] F) (p : ι → E) (q : ι → F) :
    ∑ i, ‖R (p i) - q i‖ ^ 2 =
      ∑ i, ‖p i‖ ^ 2 + ∑ i, ‖q i‖ ^ 2 - 2 * crossCorrelation R p q := by
  simp_rw [norm_sub_sq_real, LinearIsometry.norm_map, crossCorrelation, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => by ring

/-- **Minimising the residual over isometries is maximising the correlation**. -/
theorem sum_norm_sub_sq_le_iff (R R' : E →ₗᵢ[ℝ] F) (p : ι → E) (q : ι → F) :
    ∑ i, ‖R (p i) - q i‖ ^ 2 ≤ ∑ i, ‖R' (p i) - q i‖ ^ 2 ↔
      crossCorrelation R' p q ≤ crossCorrelation R p q := by
  rw [sum_norm_sub_sq_isometry, sum_norm_sub_sq_isometry]
  constructor <;> intro h <;> linarith

/-- **Kabsch / Umeyama reduction**: if the isometry `R` maximises the correlation of the centred
clouds over all isometries, then `R` with its optimal translation `q̄ - R p̄` minimises
`J(R', t) = ∑ ‖R' pᵢ + t - qᵢ‖²` over all isometries `R'` and translations `t`. -/
theorem registrationCost_le_of_crossCorrelation_max [Nonempty ι] (R : E →ₗᵢ[ℝ] F)
    (p : ι → E) (q : ι → F)
    (hR : ∀ R' : E →ₗᵢ[ℝ] F, crossCorrelation R' (fun i => p i - centroid p)
        (fun i => q i - centroid q) ≤
      crossCorrelation R (fun i => p i - centroid p) (fun i => q i - centroid q))
    (R' : E →ₗᵢ[ℝ] F) (t : F) :
    registrationCost R.toLinearMap p q (optimalTranslation R.toLinearMap p q) ≤
      registrationCost R'.toLinearMap p q t := by
  refine le_trans ?_ (registrationCost_optimalTranslation_le _ p q t)
  rw [registrationCost_optimalTranslation, registrationCost_optimalTranslation]
  exact (sum_norm_sub_sq_le_iff R R' (fun i => p i - centroid p)
    (fun i => q i - centroid q)).2 (hR R')

end Rotation

section Matrix

variable {ι m n K : Type*} [Fintype ι] [Fintype m] [Fintype n] [CommRing K]

/-- The cross-covariance matrix `H = ∑ i, qᵢ pᵢᵀ`. -/
def crossCovariance (p : ι → n → K) (q : ι → m → K) : Matrix m n K :=
  ∑ i, vecMulVec (q i) (p i)

/-- **Correlation as a trace**: `∑ i, (R pᵢ) ⬝ qᵢ = tr (Rᵀ H)` with `H = ∑ qᵢ pᵢᵀ`. -/
theorem sum_mulVec_dotProduct_eq_trace (R : Matrix m n K) (p : ι → n → K) (q : ι → m → K) :
    ∑ i, (R *ᵥ p i) ⬝ᵥ q i = trace (Rᵀ * crossCovariance p q) := by
  rw [crossCovariance, Matrix.mul_sum, trace_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [trace_mul_comm, vecMulVec_mul, trace_vecMulVec, vecMul_transpose, dotProduct_comm]

/-- The trace identity with the Euclidean inner product on `EuclideanSpace ℝ (Fin d)`. -/
theorem sum_inner_toEuclideanLin_eq_trace {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ)
    (p q : ι → EuclideanSpace ℝ (Fin d)) :
    ∑ i, ⟪Matrix.toEuclideanLin R (p i), q i⟫_ℝ =
      trace (Rᵀ * crossCovariance (fun i => (p i).ofLp) (fun i => (q i).ofLp)) := by
  rw [← sum_mulVec_dotProduct_eq_trace]
  refine sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp

end Matrix

section Planar

open Real

/-- `a cos θ + b sin θ ≤ √(a² + b²)` (Cauchy–Schwarz in the plane). -/
theorem mul_cos_add_mul_sin_le (a b θ : ℝ) : a * cos θ + b * sin θ ≤ √(a ^ 2 + b ^ 2) := by
  apply le_sqrt_of_sq_le
  have := sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (a * sin θ - b * cos θ)]

/-- Equality in `mul_cos_add_mul_sin_le` at `θ = arg (a + b i)`, i.e. `atan2 (b, a)`. -/
theorem mul_cos_add_mul_sin_arg (a b : ℝ) :
    a * cos (Complex.arg ⟨a, b⟩) + b * sin (Complex.arg ⟨a, b⟩) = √(a ^ 2 + b ^ 2) := by
  by_cases hz : (⟨a, b⟩ : ℂ) = 0
  · have ha : a = 0 := congrArg Complex.re hz
    have hb : b = 0 := congrArg Complex.im hz
    subst ha hb
    simp
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]; ring_nf
  have hpos : 0 < ‖(⟨a, b⟩ : ℂ)‖ := norm_pos_iff.2 hz
  rw [Complex.cos_arg hz, Complex.sin_arg, ← hn]
  have hsq : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hn, sq_sqrt (by positivity)]
  field_simp
  linear_combination -hsq

/-- **Uniqueness of the maximiser**: for `(a, b) ≠ 0`, `a cos θ + b sin θ = √(a² + b²)` forces
`θ ≡ arg (a + b i) (mod 2π)`. -/
theorem angle_eq_arg_of_eq_sqrt {a b θ : ℝ} (hab : (⟨a, b⟩ : ℂ) ≠ 0)
    (h : a * cos θ + b * sin θ = √(a ^ 2 + b ^ 2)) :
    (θ : Real.Angle) = Complex.arg ⟨a, b⟩ := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]; ring_nf
  have hpos : 0 < √(a ^ 2 + b ^ 2) := hn ▸ norm_pos_iff.2 hab
  have hsq : √(a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := sq_sqrt (by positivity)
  have hsc := sin_sq_add_cos_sq θ
  have hperp : a * sin θ - b * cos θ = 0 := by
    have : (a * sin θ - b * cos θ) ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have hc : cos θ * √(a ^ 2 + b ^ 2) = a := by
    rw [← h]; linear_combination a * hsc - sin θ * hperp
  have hs : sin θ * √(a ^ 2 + b ^ 2) = b := by
    rw [← h]; linear_combination b * hsc + cos θ * hperp
  apply Real.Angle.cos_sin_inj
  · rw [Complex.cos_arg hab, hn, eq_div_iff hpos.ne', hc]
  · rw [Complex.sin_arg, hn, eq_div_iff hpos.ne', hs]

/-- The planar rotation matrix by angle `θ`. -/
noncomputable def rot2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos θ, -sin θ; sin θ, cos θ]

/-- **Planar correlation**: `∑ (rot2 θ pᵢ) ⬝ qᵢ = a cos θ + b sin θ` with `a = H₀₀ + H₁₁` and
`b = H₁₀ - H₀₁`, where `H = ∑ qᵢ pᵢᵀ`. -/
theorem sum_rot2_dotProduct {ι : Type*} [Fintype ι] (p q : ι → Fin 2 → ℝ) (θ : ℝ) :
    ∑ i, (rot2 θ *ᵥ p i) ⬝ᵥ q i =
      (crossCovariance p q 0 0 + crossCovariance p q 1 1) * cos θ +
        (crossCovariance p q 1 0 - crossCovariance p q 0 1) * sin θ := by
  rw [sum_mulVec_dotProduct_eq_trace]
  simp [trace, Fin.sum_univ_two, mul_apply, rot2]
  ring

/-- The planar residual `∑ ‖rot2 θ pᵢ - qᵢ‖²` (squared Euclidean norm as a dot product). -/
noncomputable def rot2Cost {ι : Type*} [Fintype ι] (p q : ι → Fin 2 → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, (rot2 θ *ᵥ p i - q i) ⬝ᵥ (rot2 θ *ᵥ p i - q i)

/-- Rotations preserve length: `∑ ‖rot2 θ pᵢ - qᵢ‖² = ∑ (‖pᵢ‖² + ‖qᵢ‖²) - 2 ∑ (rot2 θ pᵢ) ⬝ qᵢ`. -/
theorem rot2Cost_eq {ι : Type*} [Fintype ι] (p q : ι → Fin 2 → ℝ) (θ : ℝ) :
    rot2Cost p q θ = ∑ i, (p i ⬝ᵥ p i + q i ⬝ᵥ q i) - 2 * ∑ i, (rot2 θ *ᵥ p i) ⬝ᵥ q i := by
  rw [rot2Cost, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [dotProduct, Fin.sum_univ_two, mulVec, rot2, Pi.sub_apply]
  simp
  linear_combination (p i 0 ^ 2 + p i 1 ^ 2) * sin_sq_add_cos_sq θ

/-- **Optimal planar rotation**: with `H = ∑ qᵢ pᵢᵀ`, `a = H₀₀ + H₁₁`, `b = H₁₀ - H₀₁`, the
angle `θ⋆ = arg (a + b i)` (`atan2 (b, a)`) minimises `∑ ‖rot2 θ pᵢ - qᵢ‖²` over all `θ`. -/
theorem rot2Cost_arg_le {ι : Type*} [Fintype ι] (p q : ι → Fin 2 → ℝ) (θ : ℝ) :
    rot2Cost p q (Complex.arg ⟨crossCovariance p q 0 0 + crossCovariance p q 1 1,
      crossCovariance p q 1 0 - crossCovariance p q 0 1⟩) ≤ rot2Cost p q θ := by
  rw [rot2Cost_eq, rot2Cost_eq, sum_rot2_dotProduct, sum_rot2_dotProduct,
    mul_cos_add_mul_sin_arg]
  linarith [mul_cos_add_mul_sin_le (crossCovariance p q 0 0 + crossCovariance p q 1 1)
    (crossCovariance p q 1 0 - crossCovariance p q 0 1) θ]

end Planar

end ControlsLean.Vision
