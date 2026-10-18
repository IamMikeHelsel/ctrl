module

public import LeanControls.Quantized
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! Reusable robustness certificates. These are exact-real mathematical statements:
they do not assert model fidelity or floating-point implementation correctness. -/

@[expose] public section
noncomputable section
namespace LeanControls.Certificate

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Weighted Young inequality for any nonnegative quadratic form, in any dimension.
The positive parameter trades contraction loss against disturbance amplification. -/
theorem quadratic_add_bound (Q : QuadraticForm ℝ E) (hQ : ∀ z, 0 ≤ Q z)
    {theta : ℝ} (ht : 0 < theta) (x e : E) :
    Q (x + e) ≤ (1 + theta) * Q x + (1 + theta⁻¹) * Q e := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hp := mul_nonneg ht.le (hQ (x + (-theta⁻¹) • e))
  rw [hB, Q.map_smul, (B x).map_smul] at hp
  simp only [smul_eq_mul] at hp
  rw [hB]
  have hp' : 0 ≤ theta * Q x + theta⁻¹ * Q e - B x e := by
    convert hp using 1; field_simp; ring
  linarith

/-- A nominal contraction and a quadratic error budget give an affine robust step. -/
theorem robust_step (Q : QuadraticForm ℝ E) (hQ : ∀ z, 0 ≤ Q z)
    {theta r d : ℝ} (ht : 0 < theta) (x y e : E)
    (hy : Q y ≤ r * Q x) (he : Q e ≤ d) :
    Q (y + e) ≤ ((1 + theta) * r) * Q x + (1 + theta⁻¹) * d := by
  have hsum := quadratic_add_bound Q hQ ht y e
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ 1 + theta by linarith)
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + theta⁻¹ by positivity)
  nlinarith only [hsum, hy', he']

/-- Local assumptions suffice: the one-step inequality need only hold in the
certified sublevel set, which the proof establishes inductively. -/
theorem local_invariant {V : ℕ → ℝ} {q d R : ℝ}
    (hq : 0 ≤ q) (hbudget : q * R + d ≤ R) (hinit : V 0 ≤ R)
    (hstep : ∀ n, V n ≤ R → V (n + 1) ≤ q * V n + d) :
    ∀ n, V n ≤ R := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih =>
    exact (hstep n ih).trans
      ((add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl).trans hbudget)

/-- The exact affine comparison envelope, including its steady-state floor. -/
theorem affine_envelope {V : ℕ → ℝ} {q d : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n, V (n + 1) ≤ q * V n + d) (n : ℕ) :
    V n ≤ q ^ n * (V 0 - d / (1 - q)) + d / (1 - q) := by
  have hden : 1 - q ≠ 0 := by linarith
  have hfix : q * (d / (1 - q)) + d = d / (1 - q) := by
    field_simp
    ring
  have hb := geometric_bound (V := fun k => V k - d / (1 - q)) hq
    (fun k => by have hh := hstep k; nlinarith only [hh, hfix]) n
  linarith

/-- Ultimate bound with an explicit meaning: every positive slack is eventually
respected forever. It does not claim convergence when disturbances persist. -/
theorem eventually_below_floor {V : ℕ → ℝ} {q d : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n, V (n + 1) ≤ q * V n + d)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in Filter.atTop, V n < d / (1 - q) + eps := by
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const
    (V 0 - d / (1 - q))
  simp only [zero_mul] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds heps)
  filter_upwards [hsmall] with n hn
  have hb := affine_envelope hq hq1 hstep n
  linarith

/-- A local affine certificate yields all-time safety, an explicit transient,
and the standard epsilon interpretation of an ultimate bound. -/
theorem local_affine_guarantee {V : ℕ → ℝ} {q d R : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hbudget : q * R + d ≤ R) (hinit : V 0 ≤ R)
    (hstep : ∀ n, V n ≤ R → V (n + 1) ≤ q * V n + d) :
    (∀ n, V n ≤ R) ∧
    (∀ n, V n ≤ q ^ n * (V 0 - d / (1 - q)) + d / (1 - q)) ∧
    (∀ eps > 0, ∀ᶠ n in Filter.atTop, V n < d / (1 - q) + eps) := by
  have hi := local_invariant hq hbudget hinit hstep
  have hs : ∀ n, V (n + 1) ≤ q * V n + d := fun n => hstep n (hi n)
  exact ⟨hi, affine_envelope hq hq1 hs, fun _ he => eventually_below_floor hq hq1 hs he⟩

/-- A reusable local robust-trajectory theorem. Nominal dynamics and errors may
vary arbitrarily with time; their bounds need hold only while Q stays below R. -/
theorem quadratic_trajectory (Q : QuadraticForm ℝ E) (hQ : ∀ z, 0 ≤ Q z)
    (z y e : ℕ → E) {theta r d R : ℝ} (ht : 0 < theta) (hr : 0 ≤ r)
    (hcontract : (1 + theta) * r < 1)
    (hbudget : ((1 + theta) * r) * R + (1 + theta⁻¹) * d ≤ R)
    (hinit : Q (z 0) ≤ R)
    (hdynamics : ∀ n, z (n + 1) = y n + e n)
    (hnom : ∀ n, Q (z n) ≤ R → Q (y n) ≤ r * Q (z n))
    (herr : ∀ n, Q (z n) ≤ R → Q (e n) ≤ d) :
    (∀ n, Q (z n) ≤ R) ∧
    (∀ n, Q (z n) ≤ ((1 + theta) * r) ^ n *
      (Q (z 0) - (1 + theta⁻¹) * d / (1 - (1 + theta) * r)) +
      (1 + theta⁻¹) * d / (1 - (1 + theta) * r)) ∧
    (∀ eps > 0, ∀ᶠ n in Filter.atTop,
      Q (z n) < (1 + theta⁻¹) * d / (1 - (1 + theta) * r) + eps) := by
  apply local_affine_guarantee (V := fun n => Q (z n))
    (mul_nonneg (by linarith) hr) hcontract hbudget hinit
  intro n hn
  rw [hdynamics n]
  exact robust_step Q hQ ht (z n) (y n) (e n) (hnom n hn) (herr n hn)

/-- The existing two-state PD energy, represented as a reusable quadratic form. -/
def pdForm : QuadraticForm ℝ (ℝ × ℝ) :=
  4 • (QuadraticMap.sq.comp (LinearMap.fst ℝ ℝ ℝ)) +
    QuadraticMap.sq.comp (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)

theorem pdForm_apply (z : ℝ × ℝ) : pdForm z = PD.energy z.1 z.2 := by
  simp [pdForm, QuadraticMap.sq, PD.energy]
  ring

theorem pdForm_nonneg (z : ℝ × ℝ) : 0 ≤ pdForm z := by
  rw [pdForm_apply]
  exact PD.energy_nonneg _ _

/-- Uniform multiplier after the tunable quadratic perturbation inequality. -/
def multiplier (theta hmin : ℝ) : ℝ := (1 + theta) * (1 - hmin / 6)

/-- A division-free feasibility condition for a contracting Young parameter. -/
theorem multiplier_lt_one {theta hmin : ℝ}
    (hmargin : theta * (6 - hmin) < hmin) : multiplier theta hmin < 1 := by
  unfold multiplier
  nlinarith only [hmargin]

/-- Error budget for rounded measurements and a held acceleration disturbance.
Rounding has spacing delta in both coordinates; |w| is bounded by W. -/
def disturbanceBudget (theta delta W : ℝ) : ℝ :=
  (1 + theta⁻¹) * (6 * (3 / 5 * (5 * delta / 2 + W)) ^ 2)

/-- One step of the actual rounded, clipped, disturbed update. The nominal
unrounded request fits the actuator; the rounded request may be clipped. -/
theorem pd_quantized_step {theta hmin delta U R W h x v w : ℝ}
    (ht : 0 < theta) (hd : 0 < delta) (hU : 0 ≤ U)
    (hR : 10 * R ≤ U ^ 2) (hE : PD.energy x v ≤ R)
    (hmin0 : 0 ≤ hmin) (hlo : hmin ≤ h) (hhi : h ≤ 1 / 2)
    (hw : |w| ≤ W) :
    PD.energy (x + h * v + h ^ 2 / 2 * (Quantized.input delta U x v + w))
      (v + h * (Quantized.input delta U x v + w)) ≤
      multiplier theta hmin * PD.energy x v + disturbanceBudget theta delta W := by
  have hu := RobustPD.control_within_limit hU hE hR
  let e := SampledPD.control (Quantized.quantize delta x) (Quantized.quantize delta v) -
    SampledPD.control x v
  have he : |e| ≤ 5 * delta / 2 := Quantized.quantized_control_error hd x v
  have hs := Quantized.clipping_error (e := e) hu
  have hi : SampledPD.control x v + e =
      SampledPD.control (Quantized.quantize delta x) (Quantized.quantize delta v) := by
    dsimp [e]; ring
  rw [hi] at hs
  let d := Quantized.input delta U x v - SampledPD.control x v + w
  have hdtotal : |d| ≤ 5 * delta / 2 + W := by
    dsimp [d, Quantized.input]
    exact (abs_add_le _ _).trans (add_le_add (hs.trans he) hw)
  have he2 := Quantized.integrated_error (hmin0.trans hlo) hhi hdtotal
  have hqe : pdForm (h ^ 2 / 2 * d, h * d) ≤
      6 * (3 / 5 * (5 * delta / 2 + W)) ^ 2 := by
    rw [pdForm_apply]
    exact (PD.energy_upper _ _).trans (mul_le_mul_of_nonneg_left he2 (by norm_num))
  have hnom : pdForm (SampledPD.position h x v, SampledPD.velocity h x v) ≤
      (1 - hmin / 6) * pdForm (x, v) := by
    simp only [pdForm_apply]
    exact (Sampling.half_step_contract (hmin0.trans hlo) hhi _ _).trans
      (mul_le_mul_of_nonneg_right (by linarith) (PD.energy_nonneg _ _))
  have hb := robust_step pdForm pdForm_nonneg ht (x, v)
    (SampledPD.position h x v, SampledPD.velocity h x v) (h ^ 2 / 2 * d, h * d) hnom hqe
  simp only [pdForm_apply, Prod.fst_add, Prod.snd_add] at hb
  have hp : x + h * v + h ^ 2 / 2 * (Quantized.input delta U x v + w) =
      SampledPD.position h x v + h ^ 2 / 2 * d := by
    dsimp [SampledPD.position, d]; ring
  have hv : v + h * (Quantized.input delta U x v + w) =
      SampledPD.velocity h x v + h * d := by
    dsimp [SampledPD.velocity, d]; ring
  rw [hp, hv]
  exact hb

/-- Parameterized operating envelope for rounded, clipped feedback. The single
budget inequality exposes the tradeoff between timing, resolution, disturbance,
and radius instead of hard-coding one instance. -/
theorem pd_quantized_invariant (h x v w : ℕ → ℝ)
    {theta hmin delta U R W : ℝ}
    (ht : 0 < theta) (hd : 0 < delta) (hU : 0 ≤ U)
    (hR : 10 * R ≤ U ^ 2) (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 2)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 2) (hw : ∀ n, |w n| ≤ W)
    (hbudget : multiplier theta hmin * R + disturbanceBudget theta delta W ≤ R)
    (hinit : PD.energy (x 0) (v 0) ≤ R)
    (hx : ∀ n, x (n + 1) = x n + h n * v n + h n ^ 2 / 2 *
      (Quantized.input delta U (x n) (v n) + w n))
    (hv : ∀ n, v (n + 1) = v n + h n * (Quantized.input delta U (x n) (v n) + w n)) :
    ∀ n, PD.energy (x n) (v n) ≤ R := by
  have hq : 0 ≤ multiplier theta hmin := by
    unfold multiplier
    exact mul_nonneg (by linarith) (by linarith)
  apply local_invariant (V := fun n => PD.energy (x n) (v n)) hq hbudget hinit
  intro n hn
  rw [hx n, hv n]
  exact pd_quantized_step ht hd hU hR hn hmin0 (hlo n) (hhi n) (hw n)

/-- Safety plus transient and ultimate energy bounds for the actual sampled
rounded/clipped controller. The ultimate bound allows arbitrary persistent
held disturbances satisfying the magnitude budget. -/
theorem pd_quantized_guarantee (h x v w : ℕ → ℝ)
    {theta hmin delta U R W : ℝ}
    (ht : 0 < theta) (hd : 0 < delta) (hU : 0 ≤ U)
    (hR : 10 * R ≤ U ^ 2) (hmin0 : 0 ≤ hmin) (hminhi : hmin ≤ 1 / 2)
    (hlo : ∀ n, hmin ≤ h n) (hhi : ∀ n, h n ≤ 1 / 2) (hw : ∀ n, |w n| ≤ W)
    (hcontract : multiplier theta hmin < 1)
    (hbudget : multiplier theta hmin * R + disturbanceBudget theta delta W ≤ R)
    (hinit : PD.energy (x 0) (v 0) ≤ R)
    (hx : ∀ n, x (n + 1) = x n + h n * v n + h n ^ 2 / 2 *
      (Quantized.input delta U (x n) (v n) + w n))
    (hv : ∀ n, v (n + 1) = v n + h n * (Quantized.input delta U (x n) (v n) + w n)) :
    let q := multiplier theta hmin
    let b := disturbanceBudget theta delta W
    (∀ n, PD.energy (x n) (v n) ≤ R) ∧
    (∀ n, PD.energy (x n) (v n) ≤
      q ^ n * (PD.energy (x 0) (v 0) - b / (1 - q)) + b / (1 - q)) ∧
    (∀ eps > 0, ∀ᶠ n in Filter.atTop, PD.energy (x n) (v n) < b / (1 - q) + eps) := by
  have hq : 0 ≤ multiplier theta hmin := by
    unfold multiplier
    exact mul_nonneg (by linarith) (by linarith)
  apply local_affine_guarantee (V := fun n => PD.energy (x n) (v n))
    hq hcontract hbudget hinit
  intro n hn
  rw [hx n, hv n]
  exact pd_quantized_step ht hd hU hR hn hmin0 (hlo n) (hhi n) (hw n)

/-- A rational witness showing the symbolic operating-envelope constraints are
simultaneously satisfiable. This recovers the earlier rounded-feedback example. -/
theorem example_parameters :
    0 < (1 / 240 : ℝ) ∧ 0 < (1 / 10000 : ℝ) ∧
    0 ≤ (1 : ℝ) ∧ 10 * (1 / 10 : ℝ) ≤ (1 : ℝ) ^ 2 ∧
    0 ≤ (1 / 20 : ℝ) ∧ (1 / 20 : ℝ) ≤ 1 / 2 ∧
    multiplier (1 / 240) (1 / 20) < 1 ∧
    multiplier (1 / 240) (1 / 20) * (1 / 10) +
      disturbanceBudget (1 / 240) (1 / 10000) (1 / 4000) ≤ 1 / 10 := by
  norm_num [multiplier, disturbanceBudget]

end LeanControls.Certificate
