import ControlsLean.Estimation.KalmanBucy
import Mathlib.Analysis.Complex.Basic

/-!
# Kalman (1960/1964) LQR robustness: gain margin `[1/2, ∞)` and 60° phase margin

If `P` solves the CARE with optimal gain `K* = R⁻¹BᵀP`, then for **every** actuator gain
`β ≥ 1/2` the perturbed loop `ẋ = (A − β B K*) x` keeps `V = xᵀPx` as a strict Lyapunov function:
`(A − βBK*)ᵀP + P(A − βBK*) = −(Q + (2β − 1) K*ᵀ R K*)`.

For modern robot arms / drones this is the statement: an LQR-designed controller tolerates any
unknown actuator efficiency in `[50%, ∞)` (motor torque constant drift, battery sag, ESC scaling)
without retuning.
-/

namespace Revival1961

open Matrix ControlsLean.Estimation ControlsLean.Controls ControlsLean.Tactics

variable {n m : Type*} [Fintype n] [Fintype m]

/-- **Gain-margin Lyapunov identity.** At a CARE solution (Joseph form) with `R K* = BᵀP`,
scaling the feedback by `β` gives
`(A − βBK*)ᵀP + P(A − βBK*) = −(Q + (2β−1) K*ᵀ R K*)`. -/
theorem care_gainMargin_lyapunov {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hK : R * K = Bᵀ * P)
    (hcare : careJoseph P A B Q R K = 0) (β : ℝ) :
    (lqrClosedLoop A B (β • K))ᵀ * P + P * lqrClosedLoop A B (β • K) =
      -(Q + (2 * β - 1) • (Kᵀ * R * K)) := by
  have hopt := careJoseph_opt_eq (A := A) (Q := Q) hP hR hK
  rw [hcare] at hopt
  have hKT : Kᵀ * R = P * B := care_normal_eq_transpose hP hR hK
  have h1 : Kᵀ * Bᵀ * P = Kᵀ * R * K := by
    rw [Matrix.mul_assoc, ← hK, Matrix.mul_assoc]
  have h2 : P * B * K = Kᵀ * R * K := by rw [hKT]
  have hAP : Aᵀ * P + P * A = Kᵀ * R * K - Q := by
    calc Aᵀ * P + P * A = (Aᵀ * P + P * A - Kᵀ * R * K + Q) + (Kᵀ * R * K - Q) := by abel
      _ = Kᵀ * R * K - Q := by rw [← hopt, zero_add]
  unfold lqrClosedLoop
  simp only [transpose_sub, transpose_mul, transpose_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [show Kᵀ * Bᵀ * P = Kᵀ * R * K from h1, show P * (B * K) = Kᵀ * R * K by
    rw [← Matrix.mul_assoc, h2]]
  have e : Aᵀ * P - β • (Kᵀ * R * K) + (P * A - β • (Kᵀ * R * K)) =
      (Aᵀ * P + P * A) - (2 * β) • (Kᵀ * R * K) := by
    rw [two_mul, add_smul]; abel
  rw [e, hAP, sub_smul, one_smul]; abel

/-- **Headline: LQR gain margin `[1/2, ∞)`.** If `P, Q, R ≻ 0` and `P` solves the CARE, then for
every `β ≥ 1/2`, `V(x) = xᵀPx` is a strict Lyapunov function for `ẋ = (A − βBK*)x`:
`V(x) > 0` and `V̇(x) = 2xᵀP(A − βBK*)x < 0` for `x ≠ 0`. -/
theorem lqr_gainMargin [DecidableEq m]
    {P A : Matrix n n ℝ} {B : Matrix n m ℝ} {Q : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hP : P.PosDef) (hQ : Q.PosDef) (hR : R.PosDef)
    (hcare : careResidual P A B Q R = 0) {β : ℝ} (hβ : 1 / 2 ≤ β) {x : n → ℝ} (hx : x ≠ 0) :
    0 < quad P x ∧
      2 * (x ⬝ᵥ (P *ᵥ (lqrClosedLoop A B (β • careGain B R P) *ᵥ x))) < 0 := by
  have hP' := hP
  have hQ' := hQ
  have hR' := hR
  rw [posDef_iff_quad_pos] at hP' hQ' hR'
  have hjos : careJoseph P A B Q R (careGain B R P) = 0 := by
    rwa [careJoseph_careGain_eq_careResidual hP'.1 hR]
  refine ⟨hP'.2 x hx, ?_⟩
  rw [← quad_symm_mul_eq_two_dotProduct hP'.1,
    care_gainMargin_lyapunov hP'.1 hR'.1 (care_normal_eq hR) hjos β, quad_neg, quad_add,
    quad_smul_mat, ← quad_mulVec_rect]
  have h1 := hQ'.2 x hx
  have h2 := quad_nonneg_of_posDef hR (careGain B R P *ᵥ x)
  have h3 : 0 ≤ 2 * β - 1 := by linarith
  nlinarith [mul_nonneg h3 h2]

/-- Trajectory form: along any solution of `ẋ = (A − βBK*)x` with `β ≥ 1/2`, the energy
`xᵀPx` has derivative `−(xᵀQx + (2β−1)(K*x)ᵀR(K*x)) ≤ −xᵀQx`. -/
theorem hasDerivAt_gainMargin {P A : Matrix n n ℝ} {B : Matrix n m ℝ}
    {Q : Matrix n n ℝ} {R : Matrix m m ℝ} {K : Matrix m n ℝ}
    (hP : Pᵀ = P) (hR : Rᵀ = R) (hK : R * K = Bᵀ * P)
    (hcare : careJoseph P A B Q R K = 0) (β : ℝ)
    {x : ℝ → n → ℝ} {t : ℝ} (hx : HasVecDerivAt x (lqrClosedLoop A B (β • K) *ᵥ x t) t) :
    HasDerivAt (fun s => quad P (x s))
      (-(quad Q (x t) + (2 * β - 1) * quad R (K *ᵥ x t))) t := by
  have h := hasDerivAt_quad hP hx
  rwa [← quad_symm_mul_eq_two_dotProduct hP, care_gainMargin_lyapunov hP hR hK hcare β,
    quad_neg, quad_add, quad_smul_mat, ← quad_mulVec_rect] at h

/-- Scalar unstable plant `ẋ = a x + u`, `Q = R = 1`: the CARE root is `p = a + √(a²+1)` and
the perturbed pole `a − βp` is stable iff `β > a/p`. -/
theorem scalar_gainMargin_sharp {a : ℝ} (ha : 0 < a) :
    let p := a + Real.sqrt (a ^ 2 + 1)
    -- CARE: 2 a p − p² + 1 = 0, K* = p; closed loop pole a − β p
    2 * a * p - p ^ 2 + 1 = 0 ∧ (∀ β, a - β * p < 0 ↔ a / p < β) := by
  intro p
  have hs : Real.sqrt (a ^ 2 + 1) ^ 2 = a ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hp : 0 < p := by positivity
  refine ⟨by simp only [p]; nlinarith [hs], fun β => ?_⟩
  rw [div_lt_iff₀ hp]; constructor <;> intro h <;> linarith

/-- The instability threshold `a/p = a/(a + √(a²+1)) ↑ 1/2` as `a → ∞`, and is always `< 1/2`.
So the margin `[1/2, ∞)` is tight over the family of scalar plants. -/
theorem scalar_threshold_lt_half {a : ℝ} (ha : 0 < a) :
    a / (a + Real.sqrt (a ^ 2 + 1)) < 1 / 2 := by
  have hs : a < Real.sqrt (a ^ 2 + 1) := by
    exact (Real.lt_sqrt ha.le).2 (by linarith)
  rw [div_lt_iff₀ (by positivity)]; linarith

/-! ## Return difference (Kalman 1964), scalar case, and the 60° phase margin -/

/-- **Kalman's return-difference inequality, scalar LQR.** Plant `ẋ = a x + b u`, cost weights
`q ≥ 0`, `r > 0`, CARE `2 a p − p² b²/r + q = 0`, gain `k = b p / r`. Loop transfer
`L(s) = k b / (s − a)`. Then `|1 + L(jω)| ≥ 1` at every frequency. -/
theorem scalar_return_difference {a b q r p ω : ℝ} (hq : 0 ≤ q) (hr : 0 < r)
    (hcare : 2 * a * p - p ^ 2 * b ^ 2 / r + q = 0)
    (hden : (⟨-a, ω⟩ : ℂ) ≠ 0) :
    1 ≤ ‖1 + ((b * p / r * b : ℝ) : ℂ) / (⟨-a, ω⟩ : ℂ)‖ := by
  set k := b * p / r * b
  have hden2 : 0 < a ^ 2 + ω ^ 2 := by
    rcases (eq_or_ne a 0) with h | h
    · have : ω ≠ 0 := fun hw => hden (by apply Complex.ext <;> simp [h, hw])
      subst h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  have heq : 1 + (k : ℂ) / (⟨-a, ω⟩ : ℂ) = (⟨k - a, ω⟩ : ℂ) / (⟨-a, ω⟩ : ℂ) := by
    rw [eq_div_iff hden, add_mul, one_mul, div_mul_cancel₀ _ hden]
    apply Complex.ext <;> simp; ring
  rw [heq, norm_div]
  rw [le_div_iff₀ (norm_pos_iff.2 hden), one_mul]
  -- compare squared moduli
  have key : (-a) ^ 2 + ω ^ 2 ≤ (k - a) ^ 2 + ω ^ 2 := by
    -- (k − a)² − a² = k² − 2ak = (b²/r)·q ≥ 0 by the CARE
    have : (k - a) ^ 2 - a ^ 2 = b ^ 2 / r * q := by
      simp only [k]; field_simp
      have : q = p ^ 2 * b ^ 2 / r - 2 * a * p := by linarith
      rw [this]; field_simp; ring
    have : 0 ≤ b ^ 2 / r * q := by positivity
    nlinarith
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simpa [Complex.normSq_apply, pow_two] using key

/-- **60° phase margin from the return difference.** At a gain-crossover frequency `|L| = 1`,
`|1 + L| ≥ 1` forces `Re L ≥ −1/2`, i.e. the phase of `L` stays at least 60° away from −180°. -/
theorem phaseMargin_sixty {L : ℂ} (hL : ‖L‖ = 1) (hrd : 1 ≤ ‖1 + L‖) : -(1 / 2) ≤ L.re := by
  have h1 : Complex.normSq L = 1 := by
    rw [← Complex.sq_norm, hL]; norm_num
  have h2 : 1 ≤ Complex.normSq (1 + L) := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg (1 + L)]
  rw [Complex.normSq_apply] at h1 h2
  simp at h2
  nlinarith

end Revival1961
