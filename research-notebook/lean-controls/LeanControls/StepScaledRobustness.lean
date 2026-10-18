module

public import LeanControls.Certificate
public import LeanControls.BernsteinCertificate

/-! Elapsed-time-scaled quadratic perturbation bounds. The Young parameter
is `h * eta`, so an error of energy order `h^2` produces an additive budget
of order `h`. The zero-time endpoint is handled separately and explicitly. -/

@[expose] public section
noncomputable section
namespace LeanControls.StepScaledRobustness

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The positive-time estimate. No lower bound away from zero is required.
The nominal factor need not be assumed nonnegative for this implication. -/
theorem quadratic_step_pos (Q : QuadraticForm ℝ E) (hQ : ∀ z, 0 ≤ Q z)
    {h H eta C W : ℝ} (hh : 0 < h) (hH : h ≤ H) (heta : 0 < eta)
    (hC : 0 ≤ C) (x y e : E)
    (hnom : Q y ≤ (1 - 2 * h * eta) * Q x)
    (herr : Q e ≤ C * h ^ 2 * W ^ 2) :
    Q (y + e) ≤ (1 - h * eta) * Q x + h * C * (H + eta⁻¹) * W ^ 2 := by
  have hs := Certificate.robust_step Q hQ (mul_pos hh heta) x y e hnom herr
  have hcoeff : (1 + h * eta) * (1 - 2 * h * eta) ≤ 1 - h * eta := by
    nlinarith [sq_nonneg (h * eta)]
  have hnom' := mul_le_mul_of_nonneg_right hcoeff (hQ x)
  have hid : (1 + (h * eta)⁻¹) * (C * h ^ 2 * W ^ 2) =
      h * C * (h + eta⁻¹) * W ^ 2 := by
    field_simp
  rw [hid] at hs
  have he' := mul_le_mul_of_nonneg_right hH
    (mul_nonneg (mul_nonneg hh.le hC) (sq_nonneg W))
  nlinarith only [hs, hnom', he']

/-- Includes `h=0`, with an explicit zero error at that endpoint. The nominal
bound at zero supplies `Q y ≤ Q x`; the stronger identity `y=x` is unnecessary. -/
theorem quadratic_step (Q : QuadraticForm ℝ E) (hQ : ∀ z, 0 ≤ Q z)
    {h H eta C W : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (heta : 0 < eta)
    (hC : 0 ≤ C) (x y e : E) (hzero : h = 0 → e = 0)
    (hnom : Q y ≤ (1 - 2 * h * eta) * Q x)
    (herr : Q e ≤ C * h ^ 2 * W ^ 2) :
    Q (y + e) ≤ (1 - h * eta) * Q x + h * C * (H + eta⁻¹) * W ^ 2 := by
  rcases eq_or_lt_of_le hh with hz | hp
  · have he := hzero hz.symm
    subst h
    simpa [he] using hnom
  · exact quadratic_step_pos Q hQ hp hH heta hC x y e hnom herr

/-- The scalar invariance argument for a step-scaled additive budget.
`D` and `R` need no independent sign assumptions for this implication. -/
theorem scaled_invariant {Vx Vy h eta D R : ℝ}
    (hh : 0 ≤ h) (hq : h * eta ≤ 1) (hbudget : D ≤ eta * R)
    (hx : Vx ≤ R) (hstep : Vy ≤ (1 - h * eta) * Vx + h * D) : Vy ≤ R := by
  have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hq)
  have hd' := mul_le_mul_of_nonneg_left hbudget hh
  nlinarith only [hstep, hx', hd']

/-- A quadratic energy sublevel is invariant at every elapsed time in `[0,H]`,
including arbitrarily small positive times and the explicit zero endpoint. -/
theorem quadratic_invariant (Q : QuadraticForm ℝ E) (hQ : ∀ z, 0 ≤ Q z)
    {h H eta C W R : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (heta : 0 < eta)
    (hC : 0 ≤ C) (hq : h * eta ≤ 1)
    (hbudget : C * (H + eta⁻¹) * W ^ 2 ≤ eta * R)
    (x y e : E) (hx : Q x ≤ R) (hzero : h = 0 → e = 0)
    (hnom : Q y ≤ (1 - 2 * h * eta) * Q x)
    (herr : Q e ≤ C * h ^ 2 * W ^ 2) : Q (y + e) ≤ R := by
  apply scaled_invariant hh hq hbudget hx
  simpa only [mul_assoc] using quadratic_step Q hQ hh hH heta hC x y e hzero hnom herr

/-- Local step assumptions give invariance for arbitrary nonnegative step
lengths; a positive minimum period is not needed for safety. -/
theorem scaled_trajectory_invariant {V : ℕ → ℝ} {h : ℕ → ℝ} {eta D R : ℝ}
    (hh : ∀ n, 0 ≤ h n) (hq : ∀ n, h n * eta ≤ 1)
    (hbudget : D ≤ eta * R) (hinit : V 0 ≤ R)
    (hstep : ∀ n, V n ≤ R → V (n + 1) ≤ (1 - h n * eta) * V n + h n * D) :
    ∀ n, V n ≤ R := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih => exact scaled_invariant (hh n) (hq n) hbudget ih (hstep n ih)

/-- Variable step lengths preserve the floor `D/eta`. A positive lower step
bound yields a geometric transient. The positive part is needed when the
initial energy is below the floor; no sign of that initial difference is assumed. -/
theorem scaled_affine_envelope {V : ℕ → ℝ} {h : ℕ → ℝ} {eta D hmin : ℝ}
    (heta : 0 < eta) (hq : hmin * eta ≤ 1)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n * eta ≤ 1)
    (hstep : ∀ n, V (n + 1) ≤ (1 - h n * eta) * V n + h n * D) (n : ℕ) :
    V n ≤ (1 - hmin * eta) ^ n * max (V 0 - D / eta) 0 + D / eta := by
  have hq0 : 0 ≤ 1 - hmin * eta := sub_nonneg.mpr hq
  have hB : 0 ≤ max (V 0 - D / eta) 0 := le_max_right _ _
  have hfix (k : ℕ) : (1 - h k * eta) * (D / eta) + h k * D = D / eta := by
    field_simp
    ring
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have hm : V 0 - D / eta ≤ max (V 0 - D / eta) 0 := le_max_left _ _
    linarith
  | succ n ih =>
    have hfactor : 1 - h n * eta ≤ 1 - hmin * eta := by
      have hm := mul_le_mul_of_nonneg_right (hlo n) heta.le
      linarith
    have hmul := mul_le_mul_of_nonneg_right hfactor
      (mul_nonneg (pow_nonneg hq0 n) hB)
    have hprev := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hhi n))
    have hs := hstep n
    rw [pow_succ]
    nlinarith only [hs, hprev, hmul, hfix n]

/-- A strictly positive minimum step gives the usual eventual interpretation
of the disturbance floor, without claiming convergence under persistent error. -/
theorem scaled_eventually_below_floor {V : ℕ → ℝ} {h : ℕ → ℝ} {eta D hmin : ℝ}
    (heta : 0 < eta) (hmin0 : 0 < hmin) (hq : hmin * eta ≤ 1)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n * eta ≤ 1)
    (hstep : ∀ n, V (n + 1) ≤ (1 - h n * eta) * V n + h n * D)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in Filter.atTop, V n < D / eta + eps := by
  have hq0 : 0 ≤ 1 - hmin * eta := sub_nonneg.mpr hq
  have hq1 : 1 - hmin * eta < 1 := by nlinarith [mul_pos hmin0 heta]
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
    (max (V 0 - D / eta) 0)
  simp only [zero_mul] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds heps)
  filter_upwards [hsmall] with n hn
  have hb := scaled_affine_envelope heta hq hlo hhi hstep n
  linarith

/-- A local variable-step certificate supplies safety, a transient envelope and
an ultimate bound with the common floor `D/eta`. -/
theorem scaled_local_guarantee {V : ℕ → ℝ} {h : ℕ → ℝ} {eta D hmin R : ℝ}
    (heta : 0 < eta) (hmin0 : 0 < hmin) (hq : hmin * eta ≤ 1)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n * eta ≤ 1)
    (hbudget : D ≤ eta * R) (hinit : V 0 ≤ R)
    (hstep : ∀ n, V n ≤ R → V (n + 1) ≤ (1 - h n * eta) * V n + h n * D) :
    (∀ n, V n ≤ R) ∧
    (∀ n, V n ≤ (1 - hmin * eta) ^ n * max (V 0 - D / eta) 0 + D / eta) ∧
    (∀ eps > 0, ∀ᶠ n in Filter.atTop, V n < D / eta + eps) := by
  have hi := scaled_trajectory_invariant (fun n => hmin0.le.trans (hlo n))
    hhi hbudget hinit hstep
  have hs : ∀ n, V (n + 1) ≤ (1 - h n * eta) * V n + h n * D :=
    fun n => hstep n (hi n)
  exact ⟨hi, scaled_affine_envelope heta hq hlo hhi hs,
    fun _ heps => scaled_eventually_below_floor heta hmin0 hq hlo hhi hs heps⟩


open Matrix BernsteinCertificate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reusable matrix energy is the standard matrix-induced quadratic form. -/
theorem matrix_quadratic_apply (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    P.toQuadraticForm' x = energy P x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', energy]

/-- Matrix version of the elapsed-time-scaled step, suitable for polynomial
transition certificates and exact held-error bounds. -/
theorem matrix_step (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    {h H eta C W : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (heta : 0 < eta)
    (hC : 0 ≤ C) (x y e : ι → ℝ) (hzero : h = 0 → e = 0)
    (hnom : energy P y ≤ (1 - 2 * h * eta) * energy P x)
    (herr : energy P e ≤ C * h ^ 2 * W ^ 2) :
    energy P (y + e) ≤
      (1 - h * eta) * energy P x + h * C * (H + eta⁻¹) * W ^ 2 := by
  have hQ : ∀ z, 0 ≤ P.toQuadraticForm' z := by
    intro z
    rw [matrix_quadratic_apply]
    exact hP.dotProduct_mulVec_nonneg z
  simpa only [matrix_quadratic_apply] using
    quadratic_step P.toQuadraticForm' hQ hh hH heta hC x y e hzero
      (by simpa only [matrix_quadratic_apply] using hnom)
      (by simpa only [matrix_quadratic_apply] using herr)

/-- Convenience wrapper for a nominal contraction rate `c/M`, taking exactly
`eta=c/(2M)`. Only positivity of `c,M` and the explicit error bound are used. -/
theorem matrix_step_of_decay (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    {h H c M C W : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (hc : 0 < c) (hM : 0 < M)
    (hC : 0 ≤ C) (x y e : ι → ℝ) (hzero : h = 0 → e = 0)
    (hnom : energy P y ≤ (1 - h * c / M) * energy P x)
    (herr : energy P e ≤ C * h ^ 2 * W ^ 2) :
    energy P (y + e) ≤ (1 - h * (c / (2 * M))) * energy P x +
      h * C * (H + (c / (2 * M))⁻¹) * W ^ 2 := by
  have heta : 0 < c / (2 * M) := div_pos hc (by positivity)
  apply matrix_step P hP hh hH heta hC x y e hzero _ herr
  convert hnom using 1
  ring

/-- Matrix energy invariance with all interval, sign and budget assumptions
explicit. Positive definiteness/coercivity is a separate obligation for travel
limits expressed as coordinate bounds. -/
theorem matrix_invariant (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    {h H eta C W R : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (heta : 0 < eta)
    (hC : 0 ≤ C) (hq : h * eta ≤ 1)
    (hbudget : C * (H + eta⁻¹) * W ^ 2 ≤ eta * R)
    (x y e : ι → ℝ) (hx : energy P x ≤ R) (hzero : h = 0 → e = 0)
    (hnom : energy P y ≤ (1 - 2 * h * eta) * energy P x)
    (herr : energy P e ≤ C * h ^ 2 * W ^ 2) : energy P (y + e) ≤ R := by
  apply scaled_invariant hh hq hbudget hx
  simpa only [mul_assoc] using matrix_step P hP hh hH heta hC x y e hzero hnom herr

/-- Invariance stated with the original nominal rate `c/M`. A nonnegative
nominal factor is a sufficient period condition for the required order step. -/
theorem matrix_invariant_of_decay (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    {h H c M C W R : ℝ} (hh : 0 ≤ h) (hH : h ≤ H) (hc : 0 < c) (hM : 0 < M)
    (hC : 0 ≤ C) (hperiod : h * c / M ≤ 1)
    (hbudget : C * (H + (c / (2 * M))⁻¹) * W ^ 2 ≤ (c / (2 * M)) * R)
    (x y e : ι → ℝ) (hx : energy P x ≤ R) (hzero : h = 0 → e = 0)
    (hnom : energy P y ≤ (1 - h * c / M) * energy P x)
    (herr : energy P e ≤ C * h ^ 2 * W ^ 2) : energy P (y + e) ≤ R := by
  have heta : 0 < c / (2 * M) := div_pos hc (by positivity)
  have hrate : 2 * (h * (c / (2 * M))) = h * c / M := by ring
  have hq : h * (c / (2 * M)) ≤ 1 := by linarith
  apply matrix_invariant P hP hh hH heta hC hq hbudget x y e hx hzero _ herr
  convert hnom using 1
  ring

/-- Explicit intersample quantifiers: every elapsed time in `[0,H]` stays in
the energy sublevel. The nominal segment and error can be arbitrary functions
provided their stated pointwise bounds and zero-error endpoint are established. -/
theorem matrix_segment_invariant (P : Matrix ι ι ℝ) (hP : P.PosSemidef)
    {H eta C W R : ℝ} (heta : 0 < eta) (hC : 0 ≤ C) (hperiod : H * eta ≤ 1)
    (hbudget : C * (H + eta⁻¹) * W ^ 2 ≤ eta * R)
    (x : ι → ℝ) (y e : ℝ → ι → ℝ) (hx : energy P x ≤ R) (hzero : e 0 = 0)
    (hnom : ∀ t, 0 ≤ t → t ≤ H → energy P (y t) ≤ (1 - 2 * t * eta) * energy P x)
    (herr : ∀ t, 0 ≤ t → t ≤ H → energy P (e t) ≤ C * t ^ 2 * W ^ 2) :
    ∀ t, 0 ≤ t → t ≤ H → energy P (y t + e t) ≤ R := by
  intro t ht hth
  have hq := (mul_le_mul_of_nonneg_right hth heta.le).trans hperiod
  apply matrix_invariant P hP ht hth heta hC hq hbudget x (y t) (e t) hx
    _ (hnom t ht hth) (herr t ht hth)
  intro hz
  simpa [hz] using hzero

end LeanControls.StepScaledRobustness
