import Mathlib

/-!
# Algebraic core of Kalman filtering / sensor fusion

Covariance-level facts underlying the Kalman filter, as used for robot state estimation:

* scalar fusion: the gain `K* = P/(P+R)` uniquely minimizes `(1-K)²P + K²R`, with minimum
  `PR/(P+R) ≤ min P R` (inverse-variance weighting);
* the Joseph form `P⁺(K) = (I-KH)P(I-KH)ᵀ + KRKᵀ` satisfies the completing-the-square identity
  `P⁺(K) = P⁺(K*) + (K-K*)S(K-K*)ᵀ` with `S = HPHᵀ + R`, `K* = PHᵀS⁻¹`, hence the Kalman gain
  is optimal in the Loewner order and minimizes the trace;
* simplified form `P⁺(K*) = (I - K*H)P = P - PHᵀS⁻¹HP`;
* information never hurts: `P - P⁺(K*) ⪰ 0`, and `P⁺ ⪰ 0`;
* the predict step `FPFᵀ + Q` preserves PSD / PD;
* scalar steady-state Riccati: unique positive fixed point and global convergence of iterates.
-/

open Matrix Filter Topology

set_option linter.unusedSectionVars false

namespace KalmanFilter

section Scalar

/-- Scalar posterior variance obtained by fusing a prior estimate of variance `P` with an
independent measurement of variance `R` using the linear update `x⁺ = x + K (y - x)`:
`(1 - K)² P + K² R`. -/
noncomputable def scalarPosterior (P R K : ℝ) : ℝ := (1 - K) ^ 2 * P + K ^ 2 * R
/-- The optimal scalar Kalman gain `K* = P / (P + R)`. -/
noncomputable def scalarGain (P R : ℝ) : ℝ := P / (P + R)

/-- Completing the square for the scalar posterior variance:
`(1-K)²P + K²R = PR/(P+R) + (P+R)(K - K*)²`. -/
theorem scalarPosterior_eq_complete_square {P R : ℝ} (hP : 0 < P) (hR : 0 < R) (K : ℝ) :
    scalarPosterior P R K = P * R / (P + R) + (P + R) * (K - scalarGain P R) ^ 2 := by
  unfold scalarPosterior scalarGain
  have : P + R ≠ 0 := by positivity
  field_simp
  ring

/-- The minimum value of the scalar posterior variance is `PR/(P+R)`. -/
theorem scalarPosterior_gain {P R : ℝ} (hP : 0 < P) (hR : 0 < R) :
    scalarPosterior P R (scalarGain P R) = P * R / (P + R) := by
  rw [scalarPosterior_eq_complete_square hP hR]; simp

/-- The gain `K* = P/(P+R)` minimizes the scalar posterior variance. -/
theorem scalarPosterior_ge {P R : ℝ} (hP : 0 < P) (hR : 0 < R) (K : ℝ) :
    scalarPosterior P R (scalarGain P R) ≤ scalarPosterior P R K := by
  rw [scalarPosterior_gain hP hR, scalarPosterior_eq_complete_square hP hR]
  have : 0 ≤ (P + R) * (K - scalarGain P R) ^ 2 := by positivity
  linarith

/-- The minimizer of the scalar posterior variance is unique. -/
theorem scalarPosterior_eq_min_iff {P R : ℝ} (hP : 0 < P) (hR : 0 < R) (K : ℝ) :
    scalarPosterior P R K = scalarPosterior P R (scalarGain P R) ↔ K = scalarGain P R := by
  constructor
  · intro h
    rw [scalarPosterior_gain hP hR, scalarPosterior_eq_complete_square hP hR] at h
    have h1 : (P + R) * (K - scalarGain P R) ^ 2 = 0 := by linarith
    have : P + R ≠ 0 := by positivity
    have h2 : (K - scalarGain P R) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h this
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    linarith
  · rintro rfl; rfl

/-- Any gain other than `K*` gives strictly larger posterior variance. -/
theorem scalarPosterior_lt_of_ne {P R : ℝ} (hP : 0 < P) (hR : 0 < R) {K : ℝ}
    (hK : K ≠ scalarGain P R) :
    scalarPosterior P R (scalarGain P R) < scalarPosterior P R K :=
  lt_of_le_of_ne (scalarPosterior_ge hP hR K)
    (fun h => hK ((scalarPosterior_eq_min_iff hP hR K).1 h.symm))

/-- The fused variance is at most the prior variance. -/
theorem scalar_fused_le_prior {P R : ℝ} (hP : 0 < P) (hR : 0 < R) :
    P * R / (P + R) ≤ P := by
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- The fused variance is at most the measurement variance. -/
theorem scalar_fused_le_noise {P R : ℝ} (hP : 0 < P) (hR : 0 < R) :
    P * R / (P + R) ≤ R := by
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- Fusion never hurts: `PR/(P+R) ≤ min P R`. -/
theorem scalar_fused_le_min {P R : ℝ} (hP : 0 < P) (hR : 0 < R) :
    P * R / (P + R) ≤ min P R :=
  le_min (scalar_fused_le_prior hP hR) (scalar_fused_le_noise hP hR)

/-- Inverse-variance weighting: the fused information (inverse variance) is the sum of the
informations, `(PR/(P+R))⁻¹ = P⁻¹ + R⁻¹`. -/
theorem scalar_fused_inv {P R : ℝ} (hP : 0 < P) (hR : 0 < R) :
    (P * R / (P + R))⁻¹ = P⁻¹ + R⁻¹ := by
  field_simp; ring

end Scalar

section Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Joseph-form posterior covariance for an arbitrary gain `K`:
`P⁺(K) = (I - K H) P (I - K H)ᵀ + K R Kᵀ`. Valid for any gain (not only the optimal one). -/
def joseph (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ) (K : Matrix n m ℝ) :
    Matrix n n ℝ :=
  (1 - K * H) * P * (1 - K * H)ᵀ + K * R * Kᵀ

/-- Innovation covariance `S = H P Hᵀ + R`. -/
def innovCov (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ) : Matrix m m ℝ :=
  H * P * Hᵀ + R

/-- The Kalman gain `K* = P Hᵀ S⁻¹`. -/
noncomputable def kalmanGain (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ) :
    Matrix n m ℝ :=
  P * Hᵀ * (innovCov P H R)⁻¹

/-- Expanded Joseph form: `P⁺(K) = P - K H P - P Hᵀ Kᵀ + K S Kᵀ`. -/
lemma joseph_expand (P : Matrix n n ℝ) (H : Matrix m n ℝ) (R : Matrix m m ℝ)
    (K : Matrix n m ℝ) :
    joseph P H R K = P - K * H * P - P * Hᵀ * Kᵀ + K * innovCov P H R * Kᵀ := by
  simp only [joseph, innovCov, transpose_sub, transpose_one, transpose_mul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

variable {P : Matrix n n ℝ} {H : Matrix m n ℝ} {R : Matrix m m ℝ}

/-- `K* S = P Hᵀ`. -/
lemma kalmanGain_mul_innovCov (hS : (innovCov P H R).PosDef) :
    kalmanGain P H R * innovCov P H R = P * Hᵀ := by
  rw [kalmanGain, Matrix.mul_assoc, nonsing_inv_mul _ ((hS.isUnit).map detMonoidHom), Matrix.mul_one]

/-- A positive definite innovation covariance is symmetric. -/
lemma innovCov_transpose (hS : (innovCov P H R).PosDef) : (innovCov P H R)ᵀ = innovCov P H R := by
  have := hS.isHermitian
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  exact this

/-- `S K*ᵀ = H P` for symmetric `P`. -/
lemma innovCov_mul_kalmanGain_transpose (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef) :
    innovCov P H R * (kalmanGain P H R)ᵀ = H * P := by
  have h := congrArg Matrix.transpose (kalmanGain_mul_innovCov hS)
  rw [transpose_mul, transpose_mul, innovCov_transpose hS, transpose_transpose, hP] at h
  exact h



/-- **Completing the square** for the Joseph form:
`P⁺(K) = P⁺(K*) + (K - K*) S (K - K*)ᵀ`, for symmetric `P` and positive definite `S`. -/
theorem joseph_complete_square (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef) (K : Matrix n m ℝ) :
    joseph P H R K = joseph P H R (kalmanGain P H R) +
      (K - kalmanGain P H R) * innovCov P H R * (K - kalmanGain P H R)ᵀ := by
  set G := kalmanGain P H R
  set S := innovCov P H R
  have hGS : G * S = P * Hᵀ := kalmanGain_mul_innovCov hS
  have hSG : S * Gᵀ = H * P := innovCov_mul_kalmanGain_transpose hP hS
  have h1 : K * S * Gᵀ = K * H * P := by rw [Matrix.mul_assoc, hSG, Matrix.mul_assoc]
  have h2 : G * S * Kᵀ = P * Hᵀ * Kᵀ := by rw [hGS]
  have h3 : G * S * Gᵀ = G * H * P := by rw [Matrix.mul_assoc, hSG, Matrix.mul_assoc]
  have h4 : P * Hᵀ * Gᵀ = G * H * P := by rw [← hGS, h3]
  rw [joseph_expand, joseph_expand]
  simp only [Matrix.sub_mul, Matrix.mul_sub, transpose_sub]
  rw [h1, h2, h3, h4]
  abel

/-- **Loewner optimality of the Kalman gain**: `P⁺(K) - P⁺(K*)` is positive semidefinite
for every gain `K`. -/
theorem joseph_sub_optimal_posSemidef (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef)
    (K : Matrix n m ℝ) :
    (joseph P H R K - joseph P H R (kalmanGain P H R)).PosSemidef := by
  rw [joseph_complete_square hP hS K, add_sub_cancel_left]
  have := hS.posSemidef.mul_mul_conjTranspose_same (K - kalmanGain P H R)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- The Kalman gain minimizes the trace of the posterior covariance (the mean squared
estimation error): `tr P⁺(K*) ≤ tr P⁺(K)`. -/
theorem trace_joseph_optimal_le (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef)
    (K : Matrix n m ℝ) :
    (joseph P H R (kalmanGain P H R)).trace ≤ (joseph P H R K).trace := by
  have := (joseph_sub_optimal_posSemidef hP hS K).trace_nonneg
  rw [trace_sub] at this
  linarith

/-- Simplified form of the optimal posterior covariance: `P⁺(K*) = (I - K* H) P`. -/
theorem joseph_kalmanGain (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef) :
    joseph P H R (kalmanGain P H R) = (1 - kalmanGain P H R * H) * P := by
  set G := kalmanGain P H R
  have hGS : G * innovCov P H R = P * Hᵀ := kalmanGain_mul_innovCov hS
  have hSG : innovCov P H R * Gᵀ = H * P := innovCov_mul_kalmanGain_transpose hP hS
  have h3 : G * innovCov P H R * Gᵀ = G * H * P := by rw [Matrix.mul_assoc, hSG, Matrix.mul_assoc]
  have h4 : P * Hᵀ * Gᵀ = G * H * P := by rw [← hGS, h3]
  rw [joseph_expand, h3, h4, Matrix.sub_mul, Matrix.one_mul]
  abel

/-- Simplified form of the optimal posterior covariance: `P⁺(K*) = P - P Hᵀ S⁻¹ H P`. -/
theorem joseph_kalmanGain' (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef) :
    joseph P H R (kalmanGain P H R) = P - P * Hᵀ * (innovCov P H R)⁻¹ * H * P := by
  rw [joseph_kalmanGain hP hS, Matrix.sub_mul, Matrix.one_mul, kalmanGain]

/-- **Information never hurts**: `P - P⁺(K*)` is positive semidefinite, i.e. the optimal
measurement update never increases uncertainty in any direction. -/
theorem prior_sub_posterior_posSemidef (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef) :
    (P - joseph P H R (kalmanGain P H R)).PosSemidef := by
  rw [joseph_kalmanGain' hP hS, sub_sub_cancel]
  have := hS.inv.posSemidef.mul_mul_conjTranspose_same (P * Hᵀ)
  rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose, hP] at this
  simpa [Matrix.mul_assoc] using this

/-- The Joseph form is positive semidefinite for every gain when `P` and `R` are. -/
theorem joseph_posSemidef (hP : P.PosSemidef) (hR : R.PosSemidef) (K : Matrix n m ℝ) :
    (joseph P H R K).PosSemidef := by
  have h1 := hP.mul_mul_conjTranspose_same (1 - K * H)
  have h2 := hR.mul_mul_conjTranspose_same K
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact h1.add h2

/-- The optimal update does not increase the total variance: `tr P⁺(K*) ≤ tr P`. -/
theorem trace_posterior_le_prior (hP : Pᵀ = P) (hS : (innovCov P H R).PosDef) :
    (joseph P H R (kalmanGain P H R)).trace ≤ P.trace := by
  have := (prior_sub_posterior_posSemidef hP hS).trace_nonneg
  rw [trace_sub] at this; linarith

/-- If `P` is PSD and `R` is PD then the innovation covariance `S` is PD (so `K*` is
well defined). -/
theorem innovCov_posDef (hP : P.PosSemidef) (hR : R.PosDef) : (innovCov P H R).PosDef := by
  have := hP.mul_mul_conjTranspose_same H
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact Matrix.PosDef.posSemidef_add this hR

/-- Predict step covariance `P⁻ = F P Fᵀ + Q`. -/
def predictCov (F P Q : Matrix n n ℝ) : Matrix n n ℝ := F * P * Fᵀ + Q

/-- The predict step preserves positive semidefiniteness. -/
theorem predictCov_posSemidef {F P Q : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (predictCov F P Q).PosSemidef := by
  have := hP.mul_mul_conjTranspose_same F
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this.add hQ

/-- The predict step yields a positive definite covariance when `Q` is PD. -/
theorem predictCov_posDef {F P Q : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosDef) :
    (predictCov F P Q).PosDef := by
  have := hP.mul_mul_conjTranspose_same F
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact Matrix.PosDef.posSemidef_add this hQ

end Matrix

section Riccati

/-- One step of the scalar Riccati recursion for `x_{k+1} = a x_k + w` (`Var w = q`),
`y = x + v` (`Var v = r`): predict `a²p + q`, then fuse with `r`:
`p ↦ (a²p + q) r / (a²p + q + r)`. -/
noncomputable def riccatiMap (a q r p : ℝ) : ℝ := (a ^ 2 * p + q) * r / (a ^ 2 * p + q + r)

variable {a q r : ℝ}

/-- `f(p) = r - r²/(a²p + q + r)`. -/
lemma riccatiMap_eq (hq : 0 < q) (hr : 0 < r) {p : ℝ} (hp : 0 ≤ p) :
    riccatiMap a q r p = r - r ^ 2 / (a ^ 2 * p + q + r) := by
  have : 0 < a ^ 2 * p + q + r := by positivity
  unfold riccatiMap
  field_simp
  ring

/-- The Riccati map is positive on `[0, ∞)`. -/
lemma riccatiMap_pos (hq : 0 < q) (hr : 0 < r) {p : ℝ} (hp : 0 ≤ p) :
    0 < riccatiMap a q r p := by
  unfold riccatiMap; positivity

/-- The Riccati map is bounded by the measurement variance `r`. -/
lemma riccatiMap_lt (hq : 0 < q) (hr : 0 < r) {p : ℝ} (hp : 0 ≤ p) :
    riccatiMap a q r p < r := by
  rw [riccatiMap_eq hq hr hp]
  have : 0 < r ^ 2 / (a ^ 2 * p + q + r) := by positivity
  linarith

/-- The Riccati map is monotone on `[0, ∞)`. -/
lemma riccatiMap_mono (hq : 0 < q) (hr : 0 < r) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    riccatiMap a q r x ≤ riccatiMap a q r y := by
  rw [riccatiMap_eq hq hr hx, riccatiMap_eq hq hr (hx.trans hxy)]
  have h1 : 0 < a ^ 2 * x + q + r := by positivity
  have h2 : a ^ 2 * x + q + r ≤ a ^ 2 * y + q + r := by
    have := mul_le_mul_of_nonneg_left hxy (sq_nonneg a); linarith
  have := div_le_div_of_nonneg_left (sq_nonneg r) h1 h2
  linarith

/-- The Riccati map is continuous on `[0, ∞)`. -/
lemma riccatiMap_continuousAt (hq : 0 < q) (hr : 0 < r) {p : ℝ} (hp : 0 ≤ p) :
    ContinuousAt (riccatiMap a q r) p := by
  unfold riccatiMap
  have : a ^ 2 * p + q + r ≠ 0 := by positivity
  fun_prop (disch := assumption)

/-- Fixed points of the Riccati map are roots of the algebraic Riccati equation
`a²p² + (q + r - a²r)p - qr = 0`. -/
lemma riccati_fixed_iff (hq : 0 < q) (hr : 0 < r) {p : ℝ} (hp : 0 ≤ p) :
    riccatiMap a q r p = p ↔ a ^ 2 * p ^ 2 + (q + r - a ^ 2 * r) * p - q * r = 0 := by
  have : 0 < a ^ 2 * p + q + r := by positivity
  unfold riccatiMap
  rw [div_eq_iff this.ne']
  constructor <;> intro h <;> nlinarith

/-- **Steady-state Riccati**: the scalar Riccati map has a unique positive fixed point. -/
theorem riccati_existsUnique_fixed (hq : 0 < q) (hr : 0 < r) :
    ∃! p : ℝ, 0 < p ∧ riccatiMap a q r p = p := by
  obtain ⟨p, ⟨hp0, hpr⟩, hgp⟩ : ∃ p ∈ Set.Icc (0:ℝ) r, riccatiMap a q r p - p = 0 := by
    apply intermediate_value_Icc' hr.le
    · intro x hx
      exact ((riccatiMap_continuousAt hq hr hx.1).sub continuousAt_id).continuousWithinAt
    · constructor
      · have := riccatiMap_lt (a := a) hq hr hr.le; linarith
      · have := riccatiMap_pos (a := a) hq hr le_rfl; simpa using this.le
  have hfix : riccatiMap a q r p = p := by linarith
  have hppos : 0 < p := by
    rcases hp0.lt_or_eq with h | h
    · exact h
    · have := riccatiMap_pos (a := a) hq hr hp0; linarith
  refine ⟨p, ⟨hppos, hfix⟩, ?_⟩
  rintro p' ⟨hp', hfix'⟩
  have e1 := (riccati_fixed_iff hq hr hp0).1 hfix
  have e2 := (riccati_fixed_iff hq hr hp'.le).1 hfix'
  by_contra hne
  have hsub : (p' - p) * (a ^ 2 * (p' + p) + (q + r - a ^ 2 * r)) = 0 := by linear_combination e2 - e1
  have hc : a ^ 2 * (p' + p) + (q + r - a ^ 2 * r) = 0 := by
    rcases mul_eq_zero.1 hsub with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have : a ^ 2 * p * p' + q * r = 0 := by linear_combination -e1 + p * hc
  have : 0 < a ^ 2 * p * p' + q * r := by positivity
  linarith

/-- Iterates of the Riccati map from a nonnegative start stay nonnegative. -/
lemma riccati_iterate_nonneg (hq : 0 < q) (hr : 0 < r) {p₀ : ℝ} (hp₀ : 0 ≤ p₀) (k : ℕ) :
    0 ≤ (riccatiMap a q r)^[k] p₀ := by
  induction k with
  | zero => simpa
  | succ k ih =>
    rw [Function.iterate_succ_apply']; exact (riccatiMap_pos hq hr ih).le

/-- **Convergence of the scalar Riccati iteration**: from any initial variance `p₀ ≥ 0`, the
iterates converge to the positive fixed point (the orbit is monotone and bounded). -/
theorem riccati_tendsto (hq : 0 < q) (hr : 0 < r) {p₀ : ℝ} (hp₀ : 0 ≤ p₀)
    {pstar : ℝ} (hpos : 0 < pstar) (hfix : riccatiMap a q r pstar = pstar) :
    Tendsto (fun k => (riccatiMap a q r)^[k] p₀) atTop (𝓝 pstar) := by
  set x : ℕ → ℝ := fun k => (riccatiMap a q r)^[k] p₀ with hx
  have hnn : ∀ k, 0 ≤ x k := riccati_iterate_nonneg hq hr hp₀
  have hsucc : ∀ k, x (k + 1) = riccatiMap a q r (x k) := fun k => by
    simp [hx, Function.iterate_succ_apply']
  -- any limit `L ≥ 0` of the orbit is the fixed point
  have key : ∀ L, Tendsto x atTop (𝓝 L) → Tendsto x atTop (𝓝 pstar) := by
    intro L hL
    have hL0 : 0 ≤ L := ge_of_tendsto' hL hnn
    have h1 : Tendsto (fun k => x (k + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => x (k + 1)) atTop (𝓝 (riccatiMap a q r L)) := by
      simp only [hsucc]
      exact (riccatiMap_continuousAt hq hr hL0).tendsto.comp hL
    have hfL : riccatiMap a q r L = L := tendsto_nhds_unique h2 h1
    have hLpos : 0 < L := by
      have := riccatiMap_pos (a := a) hq hr hL0; linarith
    obtain ⟨u, -, hu⟩ := riccati_existsUnique_fixed (a := a) hq hr
    have : L = pstar := (hu L ⟨hLpos, hfL⟩).trans (hu pstar ⟨hpos, hfix⟩).symm
    rwa [← this]
  rcases le_total (x 0) (x 1) with h01 | h10
  · have hmono : Monotone x := by
      refine monotone_nat_of_le_succ fun k => ?_
      induction k with
      | zero => exact h01
      | succ k ih =>
        have := riccatiMap_mono (a := a) hq hr (hnn k) ih; rwa [← hsucc, ← hsucc] at this
    have hbdd : BddAbove (Set.range x) := by
      refine ⟨max p₀ r, ?_⟩
      rintro _ ⟨k, rfl⟩
      cases k with
      | zero => simp [hx]
      | succ k => rw [hsucc]; exact (riccatiMap_lt hq hr (hnn k)).le.trans (le_max_right _ _)
    exact key _ (tendsto_atTop_ciSup hmono hbdd)
  · have hanti : Antitone x := by
      refine antitone_nat_of_succ_le fun k => ?_
      induction k with
      | zero => exact h10
      | succ k ih =>
        have := riccatiMap_mono (a := a) hq hr (hnn (k + 1)) ih; rwa [← hsucc, ← hsucc] at this
    have hbdd : BddBelow (Set.range x) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hnn k⟩
    exact key _ (tendsto_atTop_ciInf hanti hbdd)

end Riccati
end KalmanFilter
