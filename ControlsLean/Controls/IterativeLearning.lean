/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Instances.Matrix

/-!
# Iterative learning control in lifted (trial-domain) form

A robot repeats the same task over and over. Over one trial the plant is written in *lifted*
form `y = G u + d`, where `G : E →L[𝕜] F` maps the whole input trajectory to the whole output
trajectory and `d` is a disturbance that repeats on every trial. Given a reference `r`, the
trial-`j` error is `e_j = r - (G u_j + d)` and the learning law is
`u_{j+1} = u_j + L e_j` with a learning operator `L : F →L[𝕜] E`.

Abstract results (normed spaces over a nontrivially normed field):

* `ilc_error_succ`: `e_{j+1} = (I - G L) e_j`; `ilc_error_eq_pow`: `e_j = (I - G L)^j e_0`.
* `ilc_norm_error_succ_le`, `ilc_norm_error_le`: if `‖I - G L‖ ≤ ρ` then
  `‖e_{j+1}‖ ≤ ρ ‖e_j‖` and `‖e_j‖ ≤ ρ^j ‖e_0‖`.
* `ilc_norm_error_antitone`: if `‖I - G L‖ ≤ 1` the error norm is monotonically
  non-increasing from trial to trial.
* `ilc_error_tendsto_zero`: if `‖I - G L‖ < 1` then `e_j → 0`.
* `ilc_input_converges`: if moreover `E` is complete, `u_j → u*` with `G u* + d = r` (perfect
  tracking is achieved by the limit input), and `‖u_j - u*‖ ≤ ‖L‖ ‖e_0‖ ρ^j / (1 - ρ)`.
  No invertibility of `G` is needed: the inputs form a Cauchy sequence.

Scalar plus nilpotent (any normed field `𝕜`, any `𝕜`-algebra):

* `spectrum_algebraMap_add_subset`: if `N` is nilpotent, `spectrum 𝕜 (c + N) ⊆ {c}`.
* `tendsto_pow_algebraMap_add_of_isNilpotent`: if `N` is nilpotent and `‖c‖ < 1`, then
  `(c + N)^k → 0`.

Arimoto's condition for P-type ILC. Let `G = lowerToeplitz h` be the `n × n` lower-triangular
Toeplitz matrix of Markov parameters `h 0, h 1, …` (`h 0 = CB` is the first Markov parameter)
and take `L = γ I`:

* `one_sub_smul_lowerToeplitz_apply_of_lt`, `one_sub_smul_lowerToeplitz_apply_self`:
  `I - γ G` is lower triangular with constant diagonal `1 - γ h 0`.
* `one_sub_smul_lowerToeplitz_eq`: `I - γ G = (1 - γ h 0) I + N` with `N` strictly lower
  triangular, and `isNilpotent_of_strictLower`: such `N` is nilpotent.
* `arimoto_spectrum_subset`: `spectrum 𝕜 (I - γ G) ⊆ {1 - γ h 0}`;
  `arimoto_spectralRadius_lt_one`: if `‖1 - γ h 0‖ < 1` the spectral radius is `< 1`.
* `arimoto_tendsto_pow`: if `‖1 - γ h 0‖ < 1` then `(I - γ G)^k → 0`.
* `arimoto_error_tendsto_zero`: **Arimoto's theorem.** With `u_{j+1} = u_j + γ e_j`, the
  tracking error `e_j = r - (G u_j + d)` tends to zero whenever `‖1 - γ h 0‖ < 1`.

Not proved here: convergence of the *input* sequence in the matrix (Arimoto) setting, where
only the spectral radius, not an operator norm, is below one; and monotone (trial-to-trial)
error decrease in that setting.
-/

open Filter Topology Finset

namespace ControlsLean.Controls

/-! ### 1. Abstract lifted ILC -/

section Abstract

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : E →L[𝕜] F} {L : F →L[𝕜] E} {d r : F} {u : ℕ → E}

/-- **Error recursion.** Under `u_{j+1} = u_j + L e_j`, the error obeys
`e_{j+1} = (I - G L) e_j`. -/
theorem ilc_error_succ (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d))) (j : ℕ) :
    r - (G (u (j + 1)) + d) = (1 - G.comp L) (r - (G (u j) + d)) := by
  rw [hu j]
  simp only [map_add, FunLike.coe_sub, ContinuousLinearMap.coe_comp, Pi.sub_apply,
    Function.comp_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id', id]
  abel

/-- **Closed form.** `e_j = (I - G L)^j e_0`. -/
theorem ilc_error_eq_pow (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d))) (j : ℕ) :
    r - (G (u j) + d) = ((1 - G.comp L) ^ j) (r - (G (u 0) + d)) := by
  induction j with
  | zero => simp
  | succ j ih => rw [ilc_error_succ hu, ih, pow_succ', ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply]

/-- One-trial contraction: `‖e_{j+1}‖ ≤ ρ ‖e_j‖` whenever `‖I - G L‖ ≤ ρ`. -/
theorem ilc_norm_error_succ_le (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d)))
    {ρ : ℝ} (hρ : ‖1 - G.comp L‖ ≤ ρ) (j : ℕ) :
    ‖r - (G (u (j + 1)) + d)‖ ≤ ρ * ‖r - (G (u j) + d)‖ := by
  rw [ilc_error_succ hu]
  exact ((1 - G.comp L).le_opNorm _).trans (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))

/-- **Geometric rate.** If `‖I - G L‖ ≤ ρ` then `‖e_j‖ ≤ ρ^j ‖e_0‖`. -/
theorem ilc_norm_error_le (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d)))
    {ρ : ℝ} (hρ : ‖1 - G.comp L‖ ≤ ρ) (j : ℕ) :
    ‖r - (G (u j) + d)‖ ≤ ρ ^ j * ‖r - (G (u 0) + d)‖ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  induction j with
  | zero => simp
  | succ j ih =>
    calc ‖r - (G (u (j + 1)) + d)‖ ≤ ρ * ‖r - (G (u j) + d)‖ := ilc_norm_error_succ_le hu hρ j
      _ ≤ ρ * (ρ ^ j * ‖r - (G (u 0) + d)‖) := mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ (j + 1) * ‖r - (G (u 0) + d)‖ := by ring

/-- **Monotone convergence.** If `‖I - G L‖ ≤ 1`, the error norm never increases from one
trial to the next. -/
theorem ilc_norm_error_antitone (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d)))
    (hρ : ‖1 - G.comp L‖ ≤ 1) : Antitone fun j => ‖r - (G (u j) + d)‖ :=
  antitone_nat_of_succ_le fun j => by simpa using ilc_norm_error_succ_le hu hρ j

/-- **ILC convergence.** If `‖I - G L‖ < 1`, the tracking error tends to zero. -/
theorem ilc_error_tendsto_zero (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d)))
    (hρ : ‖1 - G.comp L‖ < 1) : Tendsto (fun j => r - (G (u j) + d)) atTop (𝓝 0) := by
  refine squeeze_zero_norm (ilc_norm_error_le hu le_rfl) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hρ).mul_const
    ‖r - (G (u 0) + d)‖

/-- **Convergence of the learned input.** If `E` is complete and `‖I - G L‖ < 1`, the inputs
converge to some `u*` achieving perfect tracking, `G u* + d = r`, with the explicit rate
`‖u_j - u*‖ ≤ ‖L‖ ‖e_0‖ ρ^j / (1 - ρ)` where `ρ = ‖I - G L‖`. -/
theorem ilc_input_converges [CompleteSpace E]
    (hu : ∀ j, u (j + 1) = u j + L (r - (G (u j) + d))) (hρ : ‖1 - G.comp L‖ < 1) :
    ∃ uStar : E, Tendsto u atTop (𝓝 uStar) ∧ G uStar + d = r ∧
      ∀ j, ‖u j - uStar‖ ≤
        ‖L‖ * ‖r - (G (u 0) + d)‖ * ‖1 - G.comp L‖ ^ j / (1 - ‖1 - G.comp L‖) := by
  set ρ := ‖1 - G.comp L‖
  set C := ‖L‖ * ‖r - (G (u 0) + d)‖
  have hstep : ∀ j, dist (u j) (u (j + 1)) ≤ C * ρ ^ j := fun j => by
    rw [dist_comm, dist_eq_norm, hu j, add_sub_cancel_left]
    calc ‖L (r - (G (u j) + d))‖ ≤ ‖L‖ * ‖r - (G (u j) + d)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (ρ ^ j * ‖r - (G (u 0) + d)‖) :=
          mul_le_mul_of_nonneg_left (ilc_norm_error_le hu le_rfl j) (norm_nonneg _)
      _ = C * ρ ^ j := by ring
  obtain ⟨uStar, hlim⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ρ C hρ hstep)
  refine ⟨uStar, hlim, ?_, fun j => ?_⟩
  · have h1 : Tendsto (fun j => r - (G (u j) + d)) atTop (𝓝 (r - (G uStar + d))) :=
      tendsto_const_nhds.sub (((G.continuous.tendsto _).comp hlim).add tendsto_const_nhds)
    exact (sub_eq_zero.1 (tendsto_nhds_unique h1 (ilc_error_tendsto_zero hu hρ))).symm
  · rw [← dist_eq_norm]
    exact dist_le_of_le_geometric_of_tendsto ρ C hρ hstep hlim j

end Abstract

/-! ### 2. Scalar plus nilpotent -/

section Nilpotent

variable {𝕜 A : Type*}

/-- The spectrum of `c + N` with `N` nilpotent is contained in `{c}`. -/
theorem spectrum_algebraMap_add_subset [Field 𝕜] [Ring A] [Algebra 𝕜 A] (c : 𝕜) {N : A}
    (hN : IsNilpotent N) : spectrum 𝕜 (algebraMap 𝕜 A c + N) ⊆ {c} := by
  intro μ hμ
  by_contra hne
  apply spectrum.mem_iff.1 hμ
  have hu : IsUnit (algebraMap 𝕜 A (μ - c)) :=
    (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hne)).map _
  have h := hN.neg.isUnit_add_left_of_commute hu (Algebra.commutes _ _).symm
  convert h using 1
  rw [map_sub]
  abel

/-- `C(k, m) c^(k - m) → 0` as `k → ∞` when `‖c‖ < 1`. -/
theorem tendsto_choose_mul_pow_sub [NormedField 𝕜] {c : 𝕜} (hc : ‖c‖ < 1) (m : ℕ) :
    Tendsto (fun k : ℕ => (k.choose m : 𝕜) * c ^ (k - m)) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat m]
  have hc' : ‖‖c‖‖ < 1 := by rwa [norm_norm]
  refine squeeze_zero_norm (fun k => ?_)
    (summable_choose_mul_geometric_of_norm_lt_one m hc').tendsto_atTop_zero
  rw [norm_mul, norm_pow, Nat.add_sub_cancel]
  gcongr
  simpa using Nat.norm_cast_le (α := 𝕜) ((k + m).choose m)

/-- **Powers of scalar plus nilpotent.** If `N` is nilpotent and `‖c‖ < 1`, then
`(c + N)^k → 0`. -/
theorem tendsto_pow_algebraMap_add_of_isNilpotent [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousSMul 𝕜 A] {c : 𝕜} (hc : ‖c‖ < 1)
    {N : A} (hN : IsNilpotent N) :
    Tendsto (fun k : ℕ => (algebraMap 𝕜 A c + N) ^ k) atTop (𝓝 0) := by
  obtain ⟨p, hp⟩ := hN
  set f : ℕ → ℕ → A := fun k m => ((k.choose m : 𝕜) * c ^ (k - m)) • N ^ m
  have hterm : ∀ k m, N ^ m * algebraMap 𝕜 A c ^ (k - m) * (k.choose m : A) = f k m := by
    intro k m
    simp only [f]
    rw [Algebra.smul_def, ← map_natCast (algebraMap 𝕜 A), ← map_pow, mul_assoc, ← map_mul,
      ← Algebra.commutes, mul_comm (c ^ _)]
  have key : ∀ k, (algebraMap 𝕜 A c + N) ^ k = ∑ m ∈ range p, f k m := by
    intro k
    rw [add_comm, (show Commute N (algebraMap 𝕜 A c) from (Algebra.commutes c N).symm).add_pow]
    simp only [hterm]
    have h1 : ∑ m ∈ range (k + 1), f k m = ∑ m ∈ range (k + 1 + p), f k m :=
      sum_subset (range_subset_range.2 (by omega)) fun m _ hm => by
        simp [f, Nat.choose_eq_zero_of_lt (by simpa using hm : k < m)]
    have h2 : ∑ m ∈ range p, f k m = ∑ m ∈ range (k + 1 + p), f k m :=
      sum_subset (range_subset_range.2 (by omega)) fun m _ hm => by
        simp [f, pow_eq_zero_of_le (by simpa using hm : p ≤ m) hp]
    rw [h1, h2]
  simp only [key]
  have := tendsto_finsetSum (range p) fun m _ =>
    (tendsto_choose_mul_pow_sub hc m).smul_const (N ^ m)
  simpa using this

/-- If `N` is nilpotent and `‖c‖ < 1`, the spectral radius of `c + N` is less than one. -/
theorem spectralRadius_algebraMap_add_lt_one [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    {c : 𝕜} (hc : ‖c‖ < 1) {N : A} (hN : IsNilpotent N) :
    spectralRadius 𝕜 (algebraMap 𝕜 A c + N) < 1 := by
  refine lt_of_le_of_lt (b := (‖c‖₊ : ENNReal)) (iSup₂_le fun μ hμ => ?_) ?_
  · rw [quasispectrum_eq_spectrum_union_zero] at hμ
    rcases hμ with hμ | hμ
    · rw [spectrum_algebraMap_add_subset c hN hμ]
    · rw [Set.mem_singleton_iff.1 hμ]
      simp
  · exact_mod_cast hc

end Nilpotent

/-! ### 3. Lower-triangular Toeplitz plants and Arimoto's condition -/

section Toeplitz

variable {R : Type*} {n : ℕ}

/-- The `n × n` lower-triangular Toeplitz matrix of Markov parameters `h 0, h 1, …`:
entry `(i, j)` is `h (i - j)` for `j ≤ i` and `0` above the diagonal. -/
def lowerToeplitz [Zero R] (n : ℕ) (h : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if j ≤ i then h (i.val - j.val) else 0

theorem lowerToeplitz_apply [Zero R] (h : ℕ → R) (i j : Fin n) :
    lowerToeplitz n h i j = if j ≤ i then h (i.val - j.val) else 0 := rfl

/-- A strictly lower-triangular square matrix is nilpotent: `N ^ n = 0`. -/
theorem isNilpotent_of_strictLower [CommRing R] (N : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j, i ≤ j → N i j = 0) : IsNilpotent N := by
  have key : ∀ k (i j : Fin n), i.val < j.val + k → (N ^ k) i j = 0 := by
    intro k
    induction k with
    | zero =>
      intro i j hij
      simp only [pow_zero]
      exact Matrix.one_apply_ne (Fin.ne_of_lt (by simpa using hij))
    | succ k ih =>
      intro i j hij
      rw [pow_succ', Matrix.mul_apply]
      refine sum_eq_zero fun l _ => ?_
      by_cases hil : i ≤ l
      · rw [hN i l hil, zero_mul]
      · rw [ih l j (by rw [not_le, Fin.lt_def] at hil; omega), mul_zero]
  exact ⟨n, Matrix.ext fun i j => by simpa using key n i j (by omega)⟩

variable {𝕜 : Type*} [Field 𝕜]

/-- `I - γ G` is lower triangular. -/
theorem one_sub_smul_lowerToeplitz_apply_of_lt (γ : 𝕜) (h : ℕ → 𝕜) {i j : Fin n}
    (hij : i < j) : (1 - γ • lowerToeplitz n h) i j = 0 := by
  simp [lowerToeplitz_apply, not_le.2 hij, Matrix.one_apply_ne hij.ne]

/-- The diagonal of `I - γ G` is the constant `1 - γ h 0`. -/
theorem one_sub_smul_lowerToeplitz_apply_self (γ : 𝕜) (h : ℕ → 𝕜) (i : Fin n) :
    (1 - γ • lowerToeplitz n h) i i = 1 - γ * h 0 := by
  simp [lowerToeplitz_apply]

/-- The strictly lower-triangular part of `I - γ G`. -/
def arimotoNilpart (n : ℕ) (γ : 𝕜) (h : ℕ → 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => if j < i then -(γ * h (i.val - j.val)) else 0

theorem isNilpotent_arimotoNilpart (γ : 𝕜) (h : ℕ → 𝕜) :
    IsNilpotent (arimotoNilpart n γ h) :=
  isNilpotent_of_strictLower _ fun i j hij => by simp [arimotoNilpart, not_lt.2 hij]

/-- **Scalar plus nilpotent decomposition.** `I - γ G = (1 - γ h 0) I + N` with `N` strictly
lower triangular. -/
theorem one_sub_smul_lowerToeplitz_eq (γ : 𝕜) (h : ℕ → 𝕜) :
    1 - γ • lowerToeplitz n h =
      algebraMap 𝕜 (Matrix (Fin n) (Fin n) 𝕜) (1 - γ * h 0) + arimotoNilpart n γ h := by
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.algebraMap_matrix_apply, Matrix.smul_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [lowerToeplitz_apply, arimotoNilpart, not_le.2 hij, not_lt.2 hij.le, hij.ne,
      Matrix.one_apply_ne hij.ne]
  · simp [lowerToeplitz_apply, arimotoNilpart]
  · simp [lowerToeplitz_apply, arimotoNilpart, hij.le, hij, hij.ne',
      Matrix.one_apply_ne hij.ne']

/-- **Spectrum of the P-type ILC error matrix.** The only possible eigenvalue of `I - γ G` is
`1 - γ h 0`. -/
theorem arimoto_spectrum_subset (γ : 𝕜) (h : ℕ → 𝕜) :
    spectrum 𝕜 (1 - γ • lowerToeplitz n h) ⊆ {1 - γ * h 0} := by
  rw [one_sub_smul_lowerToeplitz_eq]
  exact spectrum_algebraMap_add_subset _ (isNilpotent_arimotoNilpart γ h)

end Toeplitz

section Arimoto

open Matrix

variable {𝕜 : Type*} [NormedField 𝕜] {n : ℕ}

/-- **Arimoto's spectral condition.** If `‖1 - γ h 0‖ < 1` then `I - γ G` has spectral
radius `< 1`. -/
theorem arimoto_spectralRadius_lt_one {γ : 𝕜} {h : ℕ → 𝕜} (hc : ‖1 - γ * h 0‖ < 1) :
    spectralRadius 𝕜 (1 - γ • lowerToeplitz n h) < 1 := by
  rw [one_sub_smul_lowerToeplitz_eq]
  exact spectralRadius_algebraMap_add_lt_one hc (isNilpotent_arimotoNilpart γ h)

/-- If `‖1 - γ h 0‖ < 1` then the powers of `I - γ G` tend to zero. -/
theorem arimoto_tendsto_pow {γ : 𝕜} {h : ℕ → 𝕜} (hc : ‖1 - γ * h 0‖ < 1) :
    Tendsto (fun k : ℕ => (1 - γ • lowerToeplitz n h) ^ k) atTop (𝓝 0) := by
  rw [one_sub_smul_lowerToeplitz_eq]
  exact tendsto_pow_algebraMap_add_of_isNilpotent hc (isNilpotent_arimotoNilpart γ h)

/-- **Arimoto's theorem for P-type ILC.** For the lifted plant `y = G u + d` with
`G = lowerToeplitz n h` and the learning law `u_{j+1} = u_j + γ e_j`, the tracking error
`e_j = r - (G u_j + d)` tends to zero whenever `‖1 - γ h 0‖ < 1`. -/
theorem arimoto_error_tendsto_zero {γ : 𝕜} {h : ℕ → 𝕜} (hc : ‖1 - γ * h 0‖ < 1)
    {d r : Fin n → 𝕜} {u : ℕ → Fin n → 𝕜}
    (hu : ∀ j, u (j + 1) = u j + γ • (r - (lowerToeplitz n h *ᵥ u j + d))) :
    Tendsto (fun j => r - (lowerToeplitz n h *ᵥ u j + d)) atTop (𝓝 0) := by
  set G := lowerToeplitz n h
  have hstep : ∀ j, r - (G *ᵥ u (j + 1) + d) = (1 - γ • G) *ᵥ (r - (G *ᵥ u j + d)) := by
    intro j
    rw [hu j, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec]
    abel
  have hpow : ∀ j, r - (G *ᵥ u j + d) = (1 - γ • G) ^ j *ᵥ (r - (G *ᵥ u 0 + d)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hstep, ih, Matrix.mulVec_mulVec, ← pow_succ']
  refine Tendsto.congr (fun j => (hpow j).symm) ?_
  have := (((continuous_id.matrix_mulVec
    (continuous_const (y := r - (G *ᵥ u 0 + d))))).tendsto 0).comp
    (arimoto_tendsto_pow (n := n) hc)
  simpa [Function.comp_def] using this

end Arimoto

end ControlsLean.Controls
