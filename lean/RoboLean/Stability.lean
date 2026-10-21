import Mathlib

/-!
# Stability theory for discrete- and continuous-time systems

Robotics/control-flavoured Lyapunov stability results.

* **Discrete Lyapunov theorem** for an arbitrary map `f : E → E` on a seminormed group:
  `discrete_lyapunov_sq_bound`, `discrete_lyapunov_norm_bound`, `discrete_lyapunov_tendsto_zero`.
* **Linear systems** `x_{k+1} = A x_k` with `V x = xᵀ P x`: Rayleigh-type bounds via compactness
  of the unit sphere (`quadForm_bounds`) and exponential stability from `P ≻ 0`, `AᵀPA - P ≺ 0`
  (`linear_lyapunov_exp_stable`, `linear_lyapunov_tendsto_zero`).
* **Converse Lyapunov theorem**: geometric decay of `A^k` gives `P = Σ (Aᵀ)^k Q A^k ≻ 0`
  solving `AᵀPA - P = -Q` (`lyapunovSum_posDef`, `lyapunovSum_equation`, `converse_lyapunov`).
* **Spectral-radius criterion** via Gelfand's formula
  (`tendsto_pow_zero_of_spectralRadius_lt_one`, `real_matrix_tendsto_pow_zero_of_spectralRadius_lt_one`).
* **Continuous time**: Grönwall-type decay `exp_decay_of_deriv_le`,
  `lyapunov_exp_decay_continuous`, and the P-controlled loop `ẋ = -k x`
  (`p_control_norm_bound`, `p_control_tendsto_zero`).
* **Small gain / set-point tracking**: `‖A‖ < 1` ⇒ `I - A` invertible and
  `x_{k+1} = A x_k + b → (I - A)⁻¹ b` (`affine_iterate_tendsto`).
-/

open Filter Topology Matrix
open scoped NNReal ENNReal RealInnerProductSpace

namespace RoboLean.Stability

/-! ## 1. Discrete Lyapunov theorem for general maps -/

/-- **Iterated Lyapunov decrease.** If `V (f x) ≤ ρ V x` for all `x` with `0 ≤ ρ`, then along
the trajectory `x_k = f^[k] x`, `V x_k ≤ ρ^k V x`. -/
theorem lyapunov_iterate_le {E : Type*} (f : E → E) (V : E → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdec : ∀ x, V (f x) ≤ ρ * V x) (x : E) (k : ℕ) : V (f^[k] x) ≤ ρ ^ k * V x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_comm (ρ ^ k) ρ, mul_assoc]
    exact (hdec _).trans (mul_le_mul_of_nonneg_left ih hρ)

/-- **Discrete Lyapunov theorem (squared-norm form).** If `c₁‖x‖² ≤ V x ≤ c₂‖x‖²` with
`c₁ > 0` and `V (f x) ≤ ρ V x` with `ρ ≥ 0`, then every trajectory satisfies the explicit
geometric bound `‖x_k‖² ≤ (c₂/c₁) ρ^k ‖x₀‖²`. -/
theorem discrete_lyapunov_sq_bound {E : Type*} [SeminormedAddCommGroup E] (f : E → E)
    (V : E → ℝ) {c₁ c₂ ρ : ℝ} (hc₁ : 0 < c₁) (hlow : ∀ x, c₁ * ‖x‖ ^ 2 ≤ V x)
    (hup : ∀ x, V x ≤ c₂ * ‖x‖ ^ 2) (hρ : 0 ≤ ρ) (hdec : ∀ x, V (f x) ≤ ρ * V x)
    (x₀ : E) (k : ℕ) : ‖f^[k] x₀‖ ^ 2 ≤ c₂ / c₁ * ρ ^ k * ‖x₀‖ ^ 2 := by
  have h := (hlow _).trans ((lyapunov_iterate_le f V hρ hdec x₀ k).trans
    (mul_le_mul_of_nonneg_left (hup x₀) (pow_nonneg hρ k)))
  rw [show c₂ / c₁ * ρ ^ k * ‖x₀‖ ^ 2 = (ρ ^ k * (c₂ * ‖x₀‖ ^ 2)) / c₁ by ring,
    le_div_iff₀ hc₁]
  linarith

/-- **Discrete Lyapunov theorem (norm form).** Under the hypotheses of
`discrete_lyapunov_sq_bound` (plus `c₂ ≥ 0`), `‖x_k‖ ≤ √(c₂/c₁) (√ρ)^k ‖x₀‖`:
exponential stability with rate `√ρ`. -/
theorem discrete_lyapunov_norm_bound {E : Type*} [SeminormedAddCommGroup E] (f : E → E)
    (V : E → ℝ) {c₁ c₂ ρ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hlow : ∀ x, c₁ * ‖x‖ ^ 2 ≤ V x)
    (hup : ∀ x, V x ≤ c₂ * ‖x‖ ^ 2) (hρ : 0 ≤ ρ) (hdec : ∀ x, V (f x) ≤ ρ * V x)
    (x₀ : E) (k : ℕ) : ‖f^[k] x₀‖ ≤ Real.sqrt (c₂ / c₁) * Real.sqrt ρ ^ k * ‖x₀‖ := by
  have h := Real.sqrt_le_sqrt (discrete_lyapunov_sq_bound f V hc₁ hlow hup hρ hdec x₀ k)
  rw [Real.sqrt_sq (norm_nonneg _)] at h
  have hc : 0 ≤ c₂ / c₁ := div_nonneg hc₂ hc₁.le
  have hk : Real.sqrt (ρ ^ k) = Real.sqrt ρ ^ k := by
    rw [show ρ ^ k = (Real.sqrt ρ ^ k) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hρ], Real.sqrt_sq (by positivity)]
  rwa [Real.sqrt_mul (mul_nonneg hc (pow_nonneg hρ k)), Real.sqrt_mul hc,
    Real.sqrt_sq (norm_nonneg _), hk] at h

/-- **Discrete Lyapunov theorem (asymptotic stability).** With `0 ≤ ρ < 1`, every trajectory
of `x_{k+1} = f x_k` converges to the origin. -/
theorem discrete_lyapunov_tendsto_zero {E : Type*} [SeminormedAddCommGroup E] (f : E → E)
    (V : E → ℝ) {c₁ c₂ ρ : ℝ} (hc₁ : 0 < c₁) (hlow : ∀ x, c₁ * ‖x‖ ^ 2 ≤ V x)
    (hup : ∀ x, V x ≤ c₂ * ‖x‖ ^ 2) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdec : ∀ x, V (f x) ≤ ρ * V x) (x₀ : E) :
    Tendsto (fun k => f^[k] x₀) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun k => ‖f^[k] x₀‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => c₂ / c₁ * ρ ^ k * ‖x₀‖ ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul (c₂ / c₁)).mul_const
        (‖x₀‖ ^ 2)
    exact squeeze_zero (fun k => by positivity)
      (discrete_lyapunov_sq_bound f V hc₁ hlow hup hρ hdec x₀) hlim
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

/-! ## 2. Linear systems with quadratic Lyapunov functions -/

/-- **Norm equivalence for quadratic-like functions.** On a finite-dimensional real normed
space, a continuous function `q` with `q (t • x) = t² q x` is bounded above by `C‖x‖²` for
some `C > 0`; if moreover `q` is positive away from `0`, it is bounded below by `c‖x‖²` for
some `c > 0`. The proof minimises/maximises `q` over the compact unit sphere. -/
theorem exists_sq_bounds_of_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : E → ℝ) (hq : Continuous q)
    (hhom : ∀ (t : ℝ) (x : E), q (t • x) = t ^ 2 * q x) :
    (∃ C, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖ ^ 2) ∧
    ((∀ x, x ≠ 0 → 0 < q x) → ∃ c, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ q x) := by
  have hq0 : q 0 = 0 := by simpa using hhom 0 0
  -- every nonzero vector is a positive multiple of a unit vector
  have hdecomp : ∀ x : E, x ≠ 0 → ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 ∧
      q x = ‖x‖ ^ 2 * q (‖x‖⁻¹ • x) := by
    intro x hx
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    refine ⟨?_, ?_⟩
    · simp [norm_smul, hn]
    · rw [← hhom, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hK : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  rcases (Metric.sphere (0 : E) 1).eq_empty_or_nonempty with hS | hS
  · -- trivial space: every vector is zero
    have hall : ∀ x : E, x = 0 := fun x => by
      by_contra hx
      have := (hdecomp x hx).1
      rw [hS] at this; exact this
    refine ⟨⟨1, one_pos, fun x => by simp [hall x, hq0]⟩, fun _ => ⟨1, one_pos, fun x => by
      simp [hall x, hq0]⟩⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨y, -, hy⟩ := hK.exists_isMaxOn hS hq.continuousOn
      refine ⟨max (q y) 1, by positivity, fun x => ?_⟩
      by_cases hx : x = 0
      · simp [hx, hq0]
      obtain ⟨hmem, heq⟩ := hdecomp x hx
      rw [heq, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hy hmem).trans (le_max_left _ _)) (by positivity)
    · intro hpos
      obtain ⟨y, hyS, hy⟩ := hK.exists_isMinOn hS hq.continuousOn
      have hy0 : y ≠ 0 := by
        rintro rfl; simp at hyS
      refine ⟨q y, hpos y hy0, fun x => ?_⟩
      by_cases hx : x = 0
      · simp [hx, hq0]
      obtain ⟨hmem, heq⟩ := hdecomp x hx
      rw [heq, mul_comm]
      exact mul_le_mul_of_nonneg_left (show q y ≤ q _ from hy hmem) (by positivity)

/-- The quadratic form `x ↦ xᵀ P x` of a real square matrix. -/
def quadForm {n : Type*} [Fintype n] (P : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)

variable {n : Type*} [Fintype n]

/-- The quadratic form is continuous. -/
theorem quadForm_continuous (P : Matrix n n ℝ) : Continuous (quadForm P) := by
  unfold quadForm; fun_prop

/-- The quadratic form is 2-homogeneous. -/
theorem quadForm_smul (P : Matrix n n ℝ) (t : ℝ) (x : n → ℝ) :
    quadForm P (t • x) = t ^ 2 * quadForm P x := by
  simp [quadForm, mulVec_smul, smul_dotProduct, dotProduct_smul]; ring

/-- A positive definite matrix has a positive quadratic form off the origin. -/
theorem quadForm_pos {P : Matrix n n ℝ} (hP : P.PosDef) {x : n → ℝ} (hx : x ≠ 0) :
    0 < quadForm P x := by
  simpa [quadForm] using hP.dotProduct_mulVec_pos hx

/-- **Rayleigh-type bounds.** For `P` positive definite there are `0 < c, C` with
`c‖x‖² ≤ xᵀPx ≤ C‖x‖²` (sup norm on `n → ℝ`). -/
theorem quadForm_bounds {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ^ 2 ≤ quadForm P x ∧ quadForm P x ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨⟨C, hC, hup⟩, hlow⟩ :=
    exists_sq_bounds_of_homogeneous (quadForm P) (quadForm_continuous P) (quadForm_smul P)
  obtain ⟨c, hc, hlow⟩ := hlow fun x hx => quadForm_pos hP hx
  exact ⟨c, C, hc, hC, fun x => ⟨hlow x, hup x⟩⟩

/-- `(Ax)ᵀ P (Ax) = xᵀ (AᵀPA) x`. -/
theorem quadForm_mulVec (P A : Matrix n n ℝ) (x : n → ℝ) :
    quadForm P (A *ᵥ x) = quadForm (Aᵀ * P * A) x := by
  simp only [quadForm, ← mulVec_mulVec, dotProduct_mulVec _ Aᵀ, vecMul_transpose]

/-- Iterating the linear map `x ↦ A x` `k` times is multiplication by `A ^ k`. -/
theorem iterate_mulVec [DecidableEq n] (A : Matrix n n ℝ) (x : n → ℝ) (k : ℕ) :
    (fun v => A *ᵥ v)^[k] x = (A ^ k) *ᵥ x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', mulVec_mulVec]

/-- **Linear Lyapunov certificate.** If `P ≻ 0` and `P - AᵀPA ≻ 0` (i.e. `AᵀPA - P` is
negative definite), then `V x = xᵀPx` is sandwiched between `c‖x‖²` and `C‖x‖²` and contracts
by a factor `ρ < 1` along `x ↦ A x`. -/
theorem linear_lyapunov_decay [DecidableEq n] (A P : Matrix n n ℝ) (hP : P.PosDef)
    (hQ : (P - Aᵀ * P * A).PosDef) :
    ∃ c C ρ, 0 < c ∧ 0 < C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      (∀ x, c * ‖x‖ ^ 2 ≤ quadForm P x ∧ quadForm P x ≤ C * ‖x‖ ^ 2) ∧
      ∀ x, quadForm P (A *ᵥ x) ≤ ρ * quadForm P x := by
  obtain ⟨c, C, hc, hC, hPb⟩ := quadForm_bounds hP
  obtain ⟨d, _D, hd, _hD, hQb⟩ := quadForm_bounds hQ
  refine ⟨c, C, max (1 - d / C) 0, hc, hC, le_max_right _ _, ?_, hPb, fun x => ?_⟩
  · rw [max_lt_iff]; exact ⟨by have := div_pos hd hC; linarith, one_pos⟩
  have hsplit : quadForm P (A *ᵥ x) = quadForm P x - quadForm (P - Aᵀ * P * A) x := by
    rw [quadForm_mulVec]; simp only [quadForm, sub_mulVec, dotProduct_sub]; ring
  have h1 := (hQb x).1
  have h2 := (hPb x).2
  have hV0 : 0 ≤ quadForm P x := le_trans (by positivity) (hPb x).1
  have h3 : d / C * quadForm P x ≤ d * ‖x‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]; nlinarith
  calc quadForm P (A *ᵥ x) ≤ (1 - d / C) * quadForm P x := by rw [hsplit]; nlinarith
    _ ≤ max (1 - d / C) 0 * quadForm P x := mul_le_mul_of_nonneg_right (le_max_left _ _) hV0

/-- **Exponential stability of `x_{k+1} = A x_k` from a Lyapunov matrix.** If `P ≻ 0` and
`AᵀPA - P ≺ 0`, then `‖A^k x‖² ≤ K ρ^k ‖x‖²` for some `K ≥ 0`, `0 ≤ ρ < 1`. -/
theorem linear_lyapunov_exp_stable [DecidableEq n] (A P : Matrix n n ℝ) (hP : P.PosDef)
    (hQ : (P - Aᵀ * P * A).PosDef) :
    ∃ K ρ, 0 ≤ K ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (x : n → ℝ) (k : ℕ), ‖(A ^ k) *ᵥ x‖ ^ 2 ≤ K * ρ ^ k * ‖x‖ ^ 2 := by
  obtain ⟨c, C, ρ, hc, hC, hρ0, hρ1, hb, hdec⟩ := linear_lyapunov_decay A P hP hQ
  refine ⟨C / c, ρ, by positivity, hρ0, hρ1, fun x k => ?_⟩
  rw [← iterate_mulVec]
  exact discrete_lyapunov_sq_bound _ _ hc (fun x => (hb x).1) (fun x => (hb x).2) hρ0 hdec x k

/-- **Asymptotic stability of `x_{k+1} = A x_k`.** If `P ≻ 0` and `AᵀPA - P ≺ 0`, every
trajectory `A^k x` converges to `0`. -/
theorem linear_lyapunov_tendsto_zero [DecidableEq n] (A P : Matrix n n ℝ) (hP : P.PosDef)
    (hQ : (P - Aᵀ * P * A).PosDef) (x : n → ℝ) :
    Tendsto (fun k : ℕ => (A ^ k) *ᵥ x) atTop (𝓝 0) := by
  obtain ⟨c, C, ρ, hc, hC, hρ0, hρ1, hb, hdec⟩ := linear_lyapunov_decay A P hP hQ
  simp_rw [← iterate_mulVec]
  exact discrete_lyapunov_tendsto_zero _ _ hc (fun x => (hb x).1) (fun x => (hb x).2) hρ0 hρ1
    hdec x

/-! ## 3. Converse Lyapunov theorem -/

section Converse

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable [DecidableEq n]

/-- The candidate Lyapunov matrix `P = Σ_k (Aᵀ)^k Q A^k` for the converse theorem. -/
noncomputable def lyapunovSum (A Q : Matrix n n ℝ) : Matrix n n ℝ :=
  ∑' k : ℕ, (Aᵀ) ^ k * Q * A ^ k

/-- If `‖A^k‖ ≤ C r^k` (Frobenius norm) with `0 ≤ r < 1`, the series `Σ (Aᵀ)^k Q A^k`
converges (it is dominated by `C²‖Q‖ (r²)^k`). -/
theorem lyapunovSum_summable {A : Matrix n n ℝ} (Q : Matrix n n ℝ) {C r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * r ^ k) :
    Summable fun k : ℕ => (Aᵀ) ^ k * Q * A ^ k := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => C ^ 2 * ‖Q‖ * (r ^ 2) ^ k) ?_ fun k => ?_
  · exact (summable_geometric_of_lt_one (by positivity)
      (by nlinarith)).mul_left _
  · calc ‖(Aᵀ) ^ k * Q * A ^ k‖ ≤ ‖(Aᵀ) ^ k‖ * ‖Q‖ * ‖A ^ k‖ := by
          refine (frobenius_norm_mul _ _).trans ?_
          gcongr; exact frobenius_norm_mul _ _
      _ = ‖A ^ k‖ ^ 2 * ‖Q‖ := by rw [← transpose_pow, frobenius_norm_transpose]; ring
      _ ≤ (C * r ^ k) ^ 2 * ‖Q‖ := by
          gcongr; exact hA k
      _ = C ^ 2 * ‖Q‖ * (r ^ 2) ^ k := by ring

/-- **Discrete Lyapunov equation.** Under geometric decay of `A^k`,
`P = Σ (Aᵀ)^k Q A^k` solves `AᵀPA - P = -Q`. -/
theorem lyapunovSum_equation {A : Matrix n n ℝ} (Q : Matrix n n ℝ) {C r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * r ^ k) :
    Aᵀ * lyapunovSum A Q * A - lyapunovSum A Q = -Q := by
  have hs := lyapunovSum_summable Q hr0 hr1 hA
  have h1 : Aᵀ * lyapunovSum A Q * A = ∑' k : ℕ, (Aᵀ) ^ (k + 1) * Q * A ^ (k + 1) := by
    rw [lyapunovSum, ← hs.tsum_mul_left, ← (hs.mul_left Aᵀ).tsum_mul_right]
    congr 1; ext1 k
    rw [pow_succ', pow_succ]; simp only [mul_assoc]
  have h2 : lyapunovSum A Q = Q + ∑' k : ℕ, (Aᵀ) ^ (k + 1) * Q * A ^ (k + 1) := by
    rw [lyapunovSum, hs.tsum_eq_zero_add]; simp
  rw [h1, h2]; abel

/-- **Positivity of the converse Lyapunov matrix.** If `Q ≻ 0` and `A^k` decays
geometrically, then `P = Σ (Aᵀ)^k Q A^k ≻ 0` (its `k = 0` term is already `Q`). -/
theorem lyapunovSum_posDef {A Q : Matrix n n ℝ} (hQ : Q.PosDef) {C r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * r ^ k) : (lyapunovSum A Q).PosDef := by
  have hs := lyapunovSum_summable Q hr0 hr1 hA
  have hQt : Qᵀ = Q := by simpa [conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, lyapunovSum, transpose_tsum]
    congr 1; ext1 k
    rw [transpose_mul, transpose_mul, transpose_pow, transpose_pow, transpose_transpose, hQt,
      mul_assoc]
  · -- the quadratic form `M ↦ xᵀ M x` is additive and continuous, so commutes with the sum
    let g : Matrix n n ℝ →+ ℝ :=
      { toFun := fun M => quadForm M x
        map_zero' := by simp [quadForm]
        map_add' := fun M N => by simp [quadForm, add_mulVec] }
    have hg : Continuous g := by
      change Continuous fun M : Matrix n n ℝ => x ⬝ᵥ (M *ᵥ x)
      fun_prop
    have hsum := hs.hasSum.map g hg
    have hle := le_hasSum hsum 0 fun k _ => by
      change 0 ≤ quadForm ((Aᵀ) ^ k * Q * A ^ k) x
      rw [← transpose_pow, ← quadForm_mulVec]
      rcases eq_or_ne (A ^ k *ᵥ x) 0 with h | h
      · simp [h, quadForm]
      · exact (quadForm_pos hQ h).le
    have h0 : (g ∘ fun k : ℕ => (Aᵀ) ^ k * Q * A ^ k) 0 = quadForm Q x := by
      simp only [Function.comp_apply, pow_zero, one_mul, mul_one]; rfl
    rw [h0] at hle
    simpa [g, quadForm, lyapunovSum] using (quadForm_pos hQ hx).trans_le hle

/-- **Converse discrete Lyapunov theorem.** If `‖A^k‖ ≤ C r^k` (Frobenius norm) with
`0 ≤ r < 1` and `Q ≻ 0`, there is `P ≻ 0` with `AᵀPA - P = -Q`, namely `P = Σ (Aᵀ)^k Q A^k`. -/
theorem converse_lyapunov {A Q : Matrix n n ℝ} (hQ : Q.PosDef) {C r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * r ^ k) :
    ∃ P : Matrix n n ℝ, P.PosDef ∧ Aᵀ * P * A - P = -Q :=
  ⟨lyapunovSum A Q, lyapunovSum_posDef hQ hr0 hr1 hA, lyapunovSum_equation Q hr0 hr1 hA⟩

end Converse

/-! ## 4. Spectral-radius criterion -/

/-- **Spectral-radius criterion, quantitative.** In a complex Banach algebra, if the spectral
radius of `a` is `< 1` then there is `r < 1` with `‖a^n‖ ≤ r^n` for all large `n`
(consequence of Gelfand's formula). -/
theorem eventually_norm_pow_le_of_spectralRadius_lt {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (h : spectralRadius ℂ a < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ r ^ n := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  refine ⟨r, r.2, by exact_mod_cast hr2, ?_⟩
  have hev := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
    (gt_mem_nhds hr1)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [one_div, ENNReal.rpow_inv_lt_iff hnpos, ENNReal.rpow_natCast, ← ENNReal.coe_pow,
    ENNReal.coe_lt_coe] at hn
  have : (‖a ^ n‖₊ : ℝ) < ((r ^ n : ℝ≥0) : ℝ) := by exact_mod_cast hn
  simpa using this.le

/-- **Spectral-radius criterion.** In a complex Banach algebra, `spectralRadius ℂ a < 1`
implies `a^n → 0`. -/
theorem tendsto_pow_zero_of_spectralRadius_lt_one {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) (h : spectralRadius ℂ a < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  obtain ⟨r, hr0, hr1, hev⟩ := eventually_norm_pow_le_of_spectralRadius_lt a h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hev
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)

section MatrixSpectral

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral-radius criterion for complex matrices (using the `L∞` operator norm to obtain
a Banach-algebra structure; the conclusion is in the standard entrywise topology). -/
theorem matrix_tendsto_pow_zero_of_spectralRadius_lt_one (A : Matrix n n ℂ)
    (h : spectralRadius ℂ A < 1) : Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) :=
  tendsto_pow_zero_of_spectralRadius_lt_one A h

end MatrixSpectral

/-- **Spectral-radius criterion for real matrices.** If the complexification of a real
matrix `A` has spectral radius `< 1`, then `A^k → 0`. -/
theorem real_matrix_tendsto_pow_zero_of_spectralRadius_lt_one {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℝ)
    (h : spectralRadius ℂ (A.map (algebraMap ℝ ℂ)) < 1) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) := by
  have hc := matrix_tendsto_pow_zero_of_spectralRadius_lt_one _ h
  have hre : Continuous fun M : Matrix n n ℂ => M.map Complex.re :=
    continuous_id.matrix_map Complex.continuous_re
  have := (hre.tendsto 0).comp hc
  convert this using 2 with k
  · simp only [Function.comp_apply, ← Matrix.map_pow]
    ext i j; simp
  · ext i j; simp

/-! ## 5. Continuous time -/

/-- **Scalar Grönwall / comparison lemma.** If `v' t ≤ -α v t` for `t ≥ 0`, then
`v t ≤ v 0 · e^{-α t}` for `t ≥ 0`. Proof: `e^{α t} v t` is antitone on `[0, ∞)`. -/
theorem exp_decay_of_deriv_le {v v' : ℝ → ℝ} {α : ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt v (v' t) t) (hle : ∀ t, 0 ≤ t → v' t ≤ -α * v t) :
    ∀ t, 0 ≤ t → v t ≤ v 0 * Real.exp (-α * t) := by
  set g : ℝ → ℝ := fun t => Real.exp (α * t) * v t with hg
  have hgd : ∀ t, 0 ≤ t → HasDerivAt g (Real.exp (α * t) * (v' t + α * v t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.exp (α * t)) (Real.exp (α * t) * α) t := by
      simpa using ((hasDerivAt_id t).const_mul α).exp
    rw [show Real.exp (α * t) * (v' t + α * v t) =
      Real.exp (α * t) * α * v t + Real.exp (α * t) * v' t by ring]
    exact h1.mul (hd t ht)
  have hanti : AntitoneOn g (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => Real.exp (α * t) * (v' t + α * v t))
      (convex_Ici 0) ?_ (fun t ht => ?_)
      (fun t ht => ?_)
    · exact fun t ht => (hgd t ht).continuousAt.continuousWithinAt
    · rw [interior_Ici] at ht
      exact (hgd t (le_of_lt ht)).hasDerivWithinAt
    · rw [interior_Ici] at ht
      have := hle t (le_of_lt ht)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  intro t ht
  have hgt : g t ≤ g 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [hg, mul_zero, Real.exp_zero, one_mul] at hgt
  have hv : v t = Real.exp (-α * t) * (Real.exp (α * t) * v t) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [hv, mul_comm (v 0)]
  exact mul_le_mul_of_nonneg_left hgt (Real.exp_pos _).le

/-- **Continuous-time Lyapunov decay.** For a trajectory `x` with velocity `x'` and a
differentiable Lyapunov function `V` with `dV(x)·x' ≤ -α V(x)`, one has
`V (x t) ≤ V (x 0) e^{-α t}` for `t ≥ 0`. -/
theorem lyapunov_exp_decay_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x x' : ℝ → E} {V : E → ℝ} {V' : E → E →L[ℝ] ℝ} {α : ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (hV : ∀ t, 0 ≤ t → HasFDerivAt V (V' (x t)) (x t))
    (hdec : ∀ t, 0 ≤ t → V' (x t) (x' t) ≤ -α * V (x t)) :
    ∀ t, 0 ≤ t → V (x t) ≤ V (x 0) * Real.exp (-α * t) :=
  exp_decay_of_deriv_le (v := fun t => V (x t)) (v' := fun t => V' (x t) (x' t))
    (fun t ht => (hV t ht).comp_hasDerivAt t (hx t ht)) hdec

/-- **Proportional control, energy bound.** A closed loop `ẋ = -k x` (e.g. error dynamics
under P-control `u = -k e`) in a real inner product space satisfies
`‖x t‖² ≤ ‖x 0‖² e^{-2k t}`, via the Lyapunov function `V x = ‖x‖²`. -/
theorem p_control_sq_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℝ → E} {k : ℝ} (hx : ∀ t, 0 ≤ t → HasDerivAt x (-k • x t) t) :
    ∀ t, 0 ≤ t → ‖x t‖ ^ 2 ≤ ‖x 0‖ ^ 2 * Real.exp (-(2 * k) * t) := by
  refine exp_decay_of_deriv_le (v' := fun t => 2 * ⟪x t, -k • x t⟫) (fun t ht => (hx t ht).norm_sq)
    fun t _ => ?_
  rw [inner_smul_right, real_inner_self_eq_norm_sq]; ring_nf; rfl

/-- **Proportional control, norm bound.** For `ẋ = -k x`, `‖x t‖ ≤ ‖x 0‖ e^{-k t}`. -/
theorem p_control_norm_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℝ → E} {k : ℝ} (hx : ∀ t, 0 ≤ t → HasDerivAt x (-k • x t) t) :
    ∀ t, 0 ≤ t → ‖x t‖ ≤ ‖x 0‖ * Real.exp (-k * t) := by
  intro t ht
  have h := Real.sqrt_le_sqrt (p_control_sq_bound hx t ht)
  have he : ‖x 0‖ ^ 2 * Real.exp (-(2 * k) * t) = (‖x 0‖ * Real.exp (-k * t)) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  rwa [Real.sqrt_sq (norm_nonneg _), he, Real.sqrt_sq (by positivity)] at h

/-- An exponential envelope `‖x t‖ ≤ ‖x 0‖ e^{-k t}` with `k > 0` forces `x t → 0`. -/
theorem tendsto_zero_of_norm_le_exp {E : Type*} [NormedAddCommGroup E] {x : ℝ → E} {k : ℝ}
    (hk : 0 < k) (hb : ∀ t, 0 ≤ t → ‖x t‖ ≤ ‖x 0‖ * Real.exp (-k * t)) :
    Tendsto x atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t => ‖x 0‖ * Real.exp (-k * t)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk)
    simpa [Function.comp_def, neg_mul] using this.const_mul ‖x 0‖
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_ge_atTop 0).mono hb) hlim

/-- **P-controlled loop converges.** For `ẋ = -k x` with gain `k > 0`, `x t → 0`. -/
theorem p_control_tendsto_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℝ → E} {k : ℝ} (hk : 0 < k) (hx : ∀ t, 0 ≤ t → HasDerivAt x (-k • x t) t) :
    Tendsto x atTop (𝓝 0) :=
  tendsto_zero_of_norm_le_exp hk (p_control_norm_bound hx)

/-! ## 6. Small gain and set-point tracking -/

section SmallGain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The steady state `x* = (I - A)⁻¹ b` of the affine iteration `x_{k+1} = A x_k + b`. -/
noncomputable def steadyState (A : E →L[ℝ] E) (b : E) : E := Ring.inverse (1 - A) b

/-- **Small-gain invertibility.** If `‖A‖ < 1` then `I - A` is invertible (Neumann series). -/
theorem isUnit_one_sub_of_norm_lt_one (A : E →L[ℝ] E) (hA : ‖A‖ < 1) : IsUnit (1 - A) :=
  ⟨Units.oneSub A hA, Units.val_oneSub A hA⟩

/-- The steady state is a fixed point: `A x* + b = x*`. -/
theorem steadyState_fixed (A : E →L[ℝ] E) (hA : ‖A‖ < 1) (b : E) :
    A (steadyState A b) + b = steadyState A b := by
  have h : (1 - A) * Ring.inverse (1 - A) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_sub_of_norm_lt_one A hA)
  have h2 : steadyState A b - A (steadyState A b) = b := by
    simpa [steadyState] using congrArg (fun T : E →L[ℝ] E => T b) h
  exact (sub_eq_iff_eq_add'.mp h2).symm

/-- **Set-point tracking error bound.** For `x_{k+1} = A x_k + b` with `‖A‖ < 1`,
`‖x_k - x*‖ ≤ ‖A‖^k ‖x₀ - x*‖`. -/
theorem affine_iterate_error (A : E →L[ℝ] E) (hA : ‖A‖ < 1) (b x₀ : E) (k : ℕ) :
    ‖(fun x => A x + b)^[k] x₀ - steadyState A b‖ ≤ ‖A‖ ^ k * ‖x₀ - steadyState A b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    conv_lhs => rw [← steadyState_fixed A hA b]
    rw [add_sub_add_right_eq_sub, ← map_sub, pow_succ, mul_comm (‖A‖ ^ k), mul_assoc]
    exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

/-- **Set-point tracking.** For `‖A‖ < 1`, the iteration `x_{k+1} = A x_k + b` converges to
`(I - A)⁻¹ b` from every initial condition. -/
theorem affine_iterate_tendsto (A : E →L[ℝ] E) (hA : ‖A‖ < 1) (b x₀ : E) :
    Tendsto (fun k => (fun x => A x + b)^[k] x₀) atTop (𝓝 (steadyState A b)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg A) hA).mul_const
    ‖x₀ - steadyState A b‖
  rw [zero_mul] at this
  exact squeeze_zero (fun _ => norm_nonneg _) (affine_iterate_error A hA b x₀) this

end SmallGain

end RoboLean.Stability
