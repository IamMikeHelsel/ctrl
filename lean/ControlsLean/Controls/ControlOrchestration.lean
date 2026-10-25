/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Control Orchestration: Stopping/Going Envelopes, Error Reconciliation & Multi-Rate Authority

This module formalizes three foundational pillars connecting safety-critical stopping/going
envelopes, multi-sensor precision reconciliation, and multi-rate control authority orchestration:

1. **Stopping, Going & Decoupled Kamm/Lorentz-Cone Safety Envelopes**:
   - `stoppingDistance`, `stopping_completion_of_squares`,
     `constant_braking_segment_le_stoppingDistance`: Exact kinematic stopping envelope
     $d_{\mathrm{stop}}(v, b) = v^2 / (2b)$ via completion of squares.
   - `coarseDelayStoppingDistance`, `rampStoppingDistance`, `transientLagSaving`,
     `transientLagSaving_eq`, `transient_lag_clearance_saving`: Exact clearance saving of a
     finite-rate linear actuator transition from $a_0$ to $-b$ over duration $\tau$ compared
     against the coarse worst-case delay envelope.
   - `stopThreshold`, `goThreshold`, `stopping_go_hysteresis_gap_pos`,
     `go_admissible_iff_headway_gt_stop_plus_hysteresis`, `no_chattering_in_hysteresis_band`:
     Positive hysteresis gap $\Delta_{\mathrm{hyst}} > 0$ separating STOP and GO switching surfaces.
   - `decoupledConeBarrier`, `decoupledConeBarrierDeriv`, `hasDerivAt_decoupledConeBarrier`,
     `decoupled_cone_barrier_deriv_eq`, `decoupled_cone_barrier_no_tangential_leakage`:
     Decoupled normal/tangential barrier certificate guaranteeing zero tangential-to-normal credit
     leakage when normal braking is deficient.
   - `headroom_derated_stopping_margin`: Exact stopping reserve inflation
     $\frac{\delta}{1 - \delta} \frac{v_n^2}{2 c_{n,0}}$ under $(1 - \delta)$ acceleration derating.

2. **Reconciliation of Errors (Multi-Sensor Precision & Innovation Orthogonal Decomposition)**:
   - `totalPrecision`, `weightedMeasurementSum`, `reconciledEstimate`,
     `reconciliationResidualEnergy`, `pairwiseDisagreementEnergy`: Precision-weighted multi-sensor
     fusion over arbitrary finite sensor ensembles.
   - `weighted_innovation_sum_zero`, `reconciliation_quadratic_completion`,
     `reconciliation_estimate_isMin`: Exact orthogonal decomposition of weighted measurement error
     into fused estimation error and internal disagreement energy.
   - `reconciliation_lagrange_pairwise_identity`, `reconciliation_disagreement_eq_pairwise`,
     `reconciliation_variance_pairwise_identity`: Exact equivalence between internal innovation
     residual energy and all-pairs precision-weighted sensor disagreement.
   - `sensorDisagreementScore`, `healthy_sensor_disagreement_le`,
     `reconciliation_fault_isolation_bound`: Certifiable fault isolation bound guaranteeing that
     any sensor exceeding the healthy pairwise threshold
     $\tau \ge W_{\mathrm{healthy}} \varepsilon^2$
     cannot belong to a $\varepsilon$-consistent healthy ensemble.
   - `effectivePrecision`, `staleness_inflated_precision_mono`,
     `staleness_inflated_precision_strict_anti`: Monotonic precision downweighting under
     measurement age $\Delta t$ and drift variance rate $\sigma_a^2$.

3. **Orchestration of Control (Multi-Rate Cascade, Simplex Authority & Pseudo-Huber Penalties)**:
   - `cbfBlendCommand`, `orchestratedCommand`, `cbfBlendVec`, `orchestratedVec`:
     3-tier control orchestrator blending nominal planning, CBF safety filtering, and Simplex
     emergency fallback.
   - `orchestrator_box_invariance`, `orchestrator_convex_hull_invariance`,
     `orchestrator_safety_margin_monotonicity`: Convex admissibility invariance and monotone safety
     barrier margin across all orchestrator modes.
   - `multi_rate_cascade_step_bound`, `multi_rate_cascade_iss_bound`,
     `multi_rate_cascade_sublevel_invariant`: Explicit $N$-step inner/outer multi-rate contraction
     and inter-rate staleness residual bound
     $\frac{1 - \rho_{\mathrm{in}}^N}{1 - \rho_{\mathrm{in}}} d_{\mathrm{out}}$.
   - `pseudoHuber`, `pseudoHuber_add_eps_sq`, `pseudoHuber_nonneg`, `pseudoHuber_le_abs`,
     `abs_sub_eps_lt_pseudoHuber`, `pseudoHuber_le_quadratic_half`,
     `pseudo_huber_bounds_and_lipschitz`: Exact algebraic square identities and linear/quadratic
     envelope bounds for the smooth Pseudo-Huber penalty
     $\phi_\varepsilon(x) = \sqrt{x^2 + \varepsilon^2} - \varepsilon$.
-/

namespace ControlsLean.Controls

open Finset Matrix

/-! ## 1. Stopping, Going & Decoupled Kamm/Lorentz-Cone Safety Envelopes -/

/-- Kinematic stopping distance $d_{\mathrm{stop}}(v, b) = \frac{v^2}{2b}$ under constant
deceleration $b$. -/
noncomputable def stoppingDistance (v b : ℝ) : ℝ :=
  v ^ 2 / (2 * b)

/-- Stopping distance is nonnegative whenever deceleration capability $b \ge 0$. -/
theorem stoppingDistance_nonneg (v : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ stoppingDistance v b := by
  unfold stoppingDistance
  positivity

/-- Stopping distance is strictly positive for nonzero speed $v \ne 0$ and $b > 0$. -/
theorem stoppingDistance_pos {v b : ℝ} (hv : v ≠ 0) (hb : 0 < b) :
    0 < stoppingDistance v b := by
  unfold stoppingDistance
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  positivity

/-- **Completion of Squares for Constant-Deceleration Displacement**:
$(2b) \left(v s - \frac{1}{2} b s^2\right) = v^2 - (v - b s)^2$. -/
theorem stopping_completion_of_squares (v b s : ℝ) :
    (2 * b) * (v * s - b * s ^ 2 / 2) = v ^ 2 - (v - b * s) ^ 2 := by
  ring

/-- **Kinematic Stopping Distance Upper-Bounds Every Point of the Braking Trajectory**:
For $b > 0$ and all elapsed braking times $s \in \mathbb{R}$,
$v s - \frac{1}{2} b s^2 \le \frac{v^2}{2b}$. -/
theorem constant_braking_segment_le_stoppingDistance (v : ℝ) {b : ℝ} (hb : 0 < b) (s : ℝ) :
    v * s - b * s ^ 2 / 2 ≤ stoppingDistance v b := by
  unfold stoppingDistance
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
  have hsq : 0 ≤ (v - b * s) ^ 2 := sq_nonneg (v - b * s)
  linarith [stopping_completion_of_squares v b s]

/-- Coarse worst-case delay stopping envelope: assumes constant pre-braking acceleration $a_0$
throughout the entire latency interval $[0, \tau]$, followed by constant deceleration $b$. -/
noncomputable def coarseDelayStoppingDistance (v₀ a₀ b τ : ℝ) : ℝ :=
  v₀ * τ + a₀ * τ ^ 2 / 2 + stoppingDistance (v₀ + a₀ * τ) b

/-- Ramp-transition stopping envelope: acceleration transitions linearly from $a_0$ to $-b$
over $[0, \tau]$, producing displacement $v_0 \tau + \frac{2 a_0 - b}{6} \tau^2$ and terminal
velocity $v_0 + \frac{a_0 - b}{2} \tau$, followed by constant deceleration $b$. -/
noncomputable def rampStoppingDistance (v₀ a₀ b τ : ℝ) : ℝ :=
  v₀ * τ + (2 * a₀ - b) * τ ^ 2 / 6 + stoppingDistance (v₀ + (a₀ - b) * τ / 2) b

/-- Explicit clearance saving of the transient ramp model over the coarse delay bound. -/
noncomputable def transientLagSaving (v₀ a₀ b τ : ℝ) : ℝ :=
  coarseDelayStoppingDistance v₀ a₀ b τ - rampStoppingDistance v₀ a₀ b τ

/-- **Exact Algebraic Factorization of the Transient-Lag Clearance Saving**:
$(24 b) \cdot \Delta d_{\mathrm{lag}}(v_0, a_0, b, \tau)
  = (a_0 + b) \tau (12 v_0 + (9 a_0 + b) \tau)$. -/
theorem transientLagSaving_eq (v₀ a₀ b τ : ℝ) (hb : b ≠ 0) :
    transientLagSaving v₀ a₀ b τ =
      (a₀ + b) * τ * (12 * v₀ + (9 * a₀ + b) * τ) / (24 * b) := by
  unfold transientLagSaving coarseDelayStoppingDistance rampStoppingDistance stoppingDistance
  have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have h24b : 24 * b ≠ 0 := mul_ne_zero (by norm_num) hb
  field_simp [h2b, h24b]
  ring

/-- **Positivity of Transient-Lag Clearance Saving**:
When $v_0 \ge 0$, $a_0 \ge 0$, $b > 0$, and $\tau > 0$, accounting for the linear actuator ramp
from $a_0$ to $-b$ strictly reduces the required stopping clearance compared to the coarse delay
envelope: $0 < \mathrm{transientLagSaving}(v_0, a_0, b, \tau)$. -/
theorem transient_lag_clearance_saving {v₀ a₀ b τ : ℝ}
    (hv₀ : 0 ≤ v₀) (ha₀ : 0 ≤ a₀) (hb : 0 < b) (hτ : 0 < τ) :
    0 < transientLagSaving v₀ a₀ b τ ∧
      rampStoppingDistance v₀ a₀ b τ < coarseDelayStoppingDistance v₀ a₀ b τ := by
  have heq := transientLagSaving_eq v₀ a₀ b τ hb.ne'
  have hpos : 0 < transientLagSaving v₀ a₀ b τ := by
    rw [heq]
    have h1 : 0 < a₀ + b := by linarith
    have h2 : 0 < 12 * v₀ + (9 * a₀ + b) * τ := by
      have : 0 < (9 * a₀ + b) * τ := mul_pos (by linarith) hτ
      linarith
    positivity
  exact ⟨hpos, sub_pos.mp hpos⟩

/-- Stopping headway threshold $r_{\mathrm{stop}} = d_{\mathrm{safe}} + \frac{v^2}{2b}$. -/
noncomputable def stopThreshold (d_safe v b : ℝ) : ℝ :=
  d_safe + stoppingDistance v b

/-- Going (resume) headway threshold
$r_{\mathrm{go}} = d_{\mathrm{safe}} + \frac{v^2}{2b} + \Delta_{\mathrm{hyst}}$
with hysteresis margin $\Delta_{\mathrm{hyst}}$. -/
noncomputable def goThreshold (d_safe v b Δ_hyst : ℝ) : ℝ :=
  stopThreshold d_safe v b + Δ_hyst

/-- **Strict Separation of Stop and Go Switching Surfaces**:
For any positive hysteresis deadband $\Delta_{\mathrm{hyst}} > 0$, the GO threshold strictly
exceeds the STOP threshold. -/
theorem stopping_go_hysteresis_gap_pos (d_safe v b : ℝ) {Δ_hyst : ℝ} (hΔ : 0 < Δ_hyst) :
    stopThreshold d_safe v b < goThreshold d_safe v b Δ_hyst := by
  unfold goThreshold
  linarith

/-- **Go-Admissibility Headway Characterization**:
The GO state is admissible ($r_{\mathrm{go}} < r$) if and only if the net obstacle clearance
$r - d_{\mathrm{safe}}$ strictly exceeds the stopping distance plus the hysteresis reserve. -/
theorem go_admissible_iff_headway_gt_stop_plus_hysteresis (r d_safe v b Δ_hyst : ℝ) :
    goThreshold d_safe v b Δ_hyst < r ↔
      stoppingDistance v b + Δ_hyst < r - d_safe := by
  unfold goThreshold stopThreshold
  constructor <;> intro h <;> linarith

/-- **Zero-Chattering Guarantee in the Hysteresis Band**:
At any range $r \le r_{\mathrm{stop}}$, the system is strictly below the GO threshold by at least
$\Delta_{\mathrm{hyst}} > 0$, so a transition into STOP cannot chatter back into GO without
accumulating at least $\Delta_{\mathrm{hyst}}$ of additional range clearance. -/
theorem no_chattering_in_hysteresis_band {r d_safe v b Δ_hyst : ℝ}
    (hstop : r ≤ stopThreshold d_safe v b) (hΔ : 0 < Δ_hyst) :
    r + Δ_hyst ≤ goThreshold d_safe v b Δ_hyst ∧ ¬ (goThreshold d_safe v b Δ_hyst < r) := by
  unfold goThreshold
  constructor <;> linarith

/-- **Decoupled Normal/Tangential Cone Barrier Function**:
$$h(r, v_n, v_t) = (r - d_{\mathrm{safe}}) - \frac{v_n^2}{2 c_n} - \mu \frac{v_t^2}{2 c_t}.$$ -/
noncomputable def decoupledConeBarrier (r d_safe v_n c_n mu v_t c_t : ℝ) : ℝ :=
  (r - d_safe) - v_n ^ 2 / (2 * c_n) - mu * v_t ^ 2 / (2 * c_t)

/-- Lie derivative of `decoupledConeBarrier` along $\dot{r} = -v_n$, $\dot{v}_n = -a_n$,
$\dot{v}_t = -a_t$. -/
noncomputable def decoupledConeBarrierDeriv (v_n c_n mu v_t c_t a_n a_t : ℝ) : ℝ :=
  -v_n + v_n * a_n / c_n + mu * v_t * a_t / c_t

/-- **Trajectory Calculus for the Decoupled Cone Barrier (`HasDerivAt`)**:
Along any smooth trajectory $(r(t), v_n(t), v_t(t))$ with $\dot{r}(t) = -v_n(t)$,
$\dot{v}_n(t) = -a_n$, and $\dot{v}_t(t) = -a_t$, the time derivative of `decoupledConeBarrier`
equals `decoupledConeBarrierDeriv`. -/
theorem hasDerivAt_decoupledConeBarrier
    (r v_n v_t : ℝ → ℝ) (t d_safe c_n mu c_t a_n a_t : ℝ)
    (hc_n : c_n ≠ 0) (hc_t : c_t ≠ 0)
    (hr : HasDerivAt r (-v_n t) t)
    (hvn : HasDerivAt v_n (-a_n) t)
    (hvt : HasDerivAt v_t (-a_t) t) :
    HasDerivAt (fun τ => decoupledConeBarrier (r τ) d_safe (v_n τ) c_n mu (v_t τ) c_t)
      (decoupledConeBarrierDeriv (v_n t) c_n mu (v_t t) c_t a_n a_t) t := by
  unfold decoupledConeBarrier decoupledConeBarrierDeriv
  have h1 : HasDerivAt (fun τ => r τ - d_safe) (-v_n t) t :=
    hr.sub_const d_safe
  have hvn_sq : HasDerivAt (fun τ => (v_n τ) ^ 2)
      (((2 : ℕ) : ℝ) * (v_n t) ^ (2 - 1) * (-a_n)) t :=
    hvn.pow 2
  have h2 : HasDerivAt (fun τ => (v_n τ) ^ 2 / (2 * c_n))
      ((((2 : ℕ) : ℝ) * (v_n t) ^ (2 - 1) * (-a_n)) / (2 * c_n)) t :=
    hvn_sq.div_const (2 * c_n)
  have hvt_sq : HasDerivAt (fun τ => (v_t τ) ^ 2)
      (((2 : ℕ) : ℝ) * (v_t t) ^ (2 - 1) * (-a_t)) t :=
    hvt.pow 2
  have h3 : HasDerivAt (fun τ => mu * (v_t τ) ^ 2 / (2 * c_t))
      ((mu * (((2 : ℕ) : ℝ) * (v_t t) ^ (2 - 1) * (-a_t))) / (2 * c_t)) t :=
    (hvt_sq.const_mul mu).div_const (2 * c_t)
  have hcomb : HasDerivAt
      (fun τ => (r τ - d_safe) - (v_n τ) ^ 2 / (2 * c_n) - mu * (v_t τ) ^ 2 / (2 * c_t))
      (-v_n t - (((2 : ℕ) : ℝ) * (v_n t) ^ (2 - 1) * (-a_n)) / (2 * c_n) -
        (mu * (((2 : ℕ) : ℝ) * (v_t t) ^ (2 - 1) * (-a_t))) / (2 * c_t)) t :=
    (h1.sub h2).sub h3
  refine hcomb.congr_deriv ?_
  push_cast
  have h2cn : 2 * c_n ≠ 0 := mul_ne_zero two_ne_zero hc_n
  have h2ct : 2 * c_t ≠ 0 := mul_ne_zero two_ne_zero hc_t
  field_simp [hc_n, hc_t, h2cn, h2ct]
  ring

/-- **Factored Form of the Decoupled Cone Barrier Derivative**:
$\dot{h} = \frac{v_n (a_n - c_n)}{c_n} + \frac{\mu v_t a_t}{c_t}$. -/
theorem decoupled_cone_barrier_deriv_eq (v_n c_n mu v_t c_t a_n a_t : ℝ) (hc_n : c_n ≠ 0) :
    decoupledConeBarrierDeriv v_n c_n mu v_t c_t a_n a_t =
      v_n * (a_n - c_n) / c_n + mu * v_t * a_t / c_t := by
  unfold decoupledConeBarrierDeriv
  field_simp [hc_n]
  ring

/-- **No Tangential-to-Normal Leakage & Decoupled Invariance Certificate**:
1. When tangential speed $v_t = 0$, closing normal speed $v_n > 0$, and normal braking is
   deficient ($a_n < c_n$), the barrier derivative is strictly negative for *every* tangential
   command $a_t \in \mathbb{R}$: tangential actuation cannot mask a normal braking deficit.
2. When decoupled normal braking $a_n \ge c_n$ (for $v_n \ge 0$) and tangential damping
   $v_t a_t \ge 0$ both hold, $\dot{h} \ge 0$ holds unconditionally. -/
theorem decoupled_cone_barrier_no_tangential_leakage
    {v_n c_n mu v_t c_t a_n a_t : ℝ} (hc_n : 0 < c_n) (hc_t : 0 < c_t) (hmu : 0 ≤ mu) :
    (0 < v_n → a_n < c_n →
      decoupledConeBarrierDeriv v_n c_n mu 0 c_t a_n a_t < 0) ∧
    (0 ≤ v_n → c_n ≤ a_n → 0 ≤ v_t * a_t →
      0 ≤ decoupledConeBarrierDeriv v_n c_n mu v_t c_t a_n a_t) := by
  constructor
  · intro hvn han
    rw [decoupled_cone_barrier_deriv_eq v_n c_n mu 0 c_t a_n a_t hc_n.ne']
    simp only [mul_zero, zero_mul, zero_div, add_zero]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hvn (sub_neg.mpr han)) hc_n
  · intro hvn han hvtat
    rw [decoupled_cone_barrier_deriv_eq v_n c_n mu v_t c_t a_n a_t hc_n.ne']
    have h_norm : 0 ≤ v_n * (a_n - c_n) / c_n := by
      have : 0 ≤ a_n - c_n := sub_nonneg.mpr han
      positivity
    have h_tang : 0 ≤ mu * v_t * a_t / c_t := by
      rw [mul_assoc]
      exact div_nonneg (mul_nonneg hmu hvtat) hc_t.le
    linarith

/-- **Headroom-Derated Stopping Margin**:
Derating normal deceleration capability from $c_{n,0}$ to $(1 - \delta) c_{n,0}$ with
$0 \le \delta < 1$ inflates the stopping distance by the exact nonnegative margin
$\frac{\delta}{1 - \delta} d_{\mathrm{stop}}(v_n, c_{n,0}) \ge 0$. -/
theorem headroom_derated_stopping_margin (v_n : ℝ) {c_n0 δ : ℝ}
    (hc_n0 : 0 < c_n0) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    stoppingDistance v_n ((1 - δ) * c_n0) - stoppingDistance v_n c_n0 =
      (δ / (1 - δ)) * stoppingDistance v_n c_n0 ∧
    0 ≤ stoppingDistance v_n ((1 - δ) * c_n0) - stoppingDistance v_n c_n0 := by
  have h1δ : 0 < 1 - δ := sub_pos.mpr hδ1
  have h_eq : stoppingDistance v_n ((1 - δ) * c_n0) - stoppingDistance v_n c_n0 =
      (δ / (1 - δ)) * stoppingDistance v_n c_n0 := by
    unfold stoppingDistance
    have hc_ne : c_n0 ≠ 0 := hc_n0.ne'
    have h1δ_ne : 1 - δ ≠ 0 := h1δ.ne'
    field_simp [hc_ne, h1δ_ne]
    ring
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  have hstop : 0 ≤ stoppingDistance v_n c_n0 := stoppingDistance_nonneg v_n hc_n0.le
  positivity

/-! ## 2. Reconciliation of Errors (Multi-Sensor Precision & Innovation Orthogonal Decomposition) -/

variable {ι : Type*}

/-- Total precision $W = \sum_{i \in s} w_i$ of a sensor ensemble $s$. -/
def totalPrecision (s : Finset ι) (w : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i

/-- Precision-weighted measurement sum $S = \sum_{i \in s} w_i y_i$. -/
def weightedMeasurementSum (s : Finset ι) (w y : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * y i

/-- Precision-weighted reconciled estimate $\hat{x} = W^{-1} \sum_{i \in s} w_i y_i$. -/
noncomputable def reconciledEstimate (s : Finset ι) (w y : ι → ℝ) : ℝ :=
  weightedMeasurementSum s w y / totalPrecision s w

/-- Weighted squared residual energy $\sum_{i \in s} w_i (y_i - x)^2$ at candidate state $x$. -/
def reconciliationResidualEnergy (s : Finset ι) (w y : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (y i - x) ^ 2

/-- Total all-pairs precision-weighted disagreement energy
$\sum_{i \in s} \sum_{j \in s} w_i w_j (y_i - y_j)^2$. -/
def pairwiseDisagreementEnergy (s : Finset ι) (w y : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * (y i - y j) ^ 2

/-- **Zero Weighted Innovation Sum**:
When $W = \sum_{i \in s} w_i \ne 0$, the precision-weighted innovations $y_i - \hat{x}$ around
the reconciled estimate $\hat{x}$ sum to zero: $\sum_{i \in s} w_i (y_i - \hat{x}) = 0$. -/
theorem weighted_innovation_sum_zero (s : Finset ι) (w y : ι → ℝ)
    (hW : totalPrecision s w ≠ 0) :
    ∑ i ∈ s, w i * (y i - reconciledEstimate s w y) = 0 := by
  have hsub : ∀ i ∈ s,
      w i * (y i - reconciledEstimate s w y) =
        w i * y i - w i * reconciledEstimate s w y := by
    intro i _
    ring
  rw [sum_congr rfl hsub, sum_sub_distrib, ← sum_mul]
  unfold reconciledEstimate weightedMeasurementSum totalPrecision at *
  rw [mul_div_cancel₀ _ hW, sub_self]

/-- **Reconciliation Orthogonal Quadratic Completion**:
For any state $x \in \mathbb{R}$ and sensor ensemble with $W = \sum_{i \in s} w_i \ne 0$,
the weighted measurement error decomposes orthogonally into fused estimation error plus
internal reconciliation residual energy:
$$\sum_{i \in s} w_i (y_i - x)^2 = W (\hat{x} - x)^2 + \sum_{i \in s} w_i (y_i - \hat{x})^2.$$ -/
theorem reconciliation_quadratic_completion (s : Finset ι) (w y : ι → ℝ) (x : ℝ)
    (hW : totalPrecision s w ≠ 0) :
    reconciliationResidualEnergy s w y x =
      totalPrecision s w * (reconciledEstimate s w y - x) ^ 2 +
        reconciliationResidualEnergy s w y (reconciledEstimate s w y) := by
  unfold reconciliationResidualEnergy
  set xhat := reconciledEstimate s w y
  have hpoint : ∀ i ∈ s,
      w i * (y i - x) ^ 2 =
        w i * (y i - xhat) ^ 2 +
          2 * (xhat - x) * (w i * (y i - xhat)) +
          w i * (xhat - x) ^ 2 := by
    intro i _
    ring
  rw [sum_congr rfl hpoint, sum_add_distrib, sum_add_distrib]
  rw [← mul_sum, weighted_innovation_sum_zero s w y hW, mul_zero, add_zero]
  rw [← sum_mul]
  unfold totalPrecision
  ring

/-- **Optimality of the Reconciled Estimate**:
When all sensor precisions are nonnegative ($w_i \ge 0$) and $W \ne 0$, the reconciled estimate
$\hat{x}$ globally minimizes $\sum_{i \in s} w_i (y_i - x)^2$ over all $x \in \mathbb{R}$. -/
theorem reconciliation_estimate_isMin (s : Finset ι) (w y : ι → ℝ) (x : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : totalPrecision s w ≠ 0) :
    reconciliationResidualEnergy s w y (reconciledEstimate s w y) ≤
      reconciliationResidualEnergy s w y x := by
  rw [reconciliation_quadratic_completion s w y x hW]
  have hW_nonneg : 0 ≤ totalPrecision s w := sum_nonneg hw
  have hterm : 0 ≤ totalPrecision s w * (reconciledEstimate s w y - x) ^ 2 :=
    mul_nonneg hW_nonneg (sq_nonneg _)
  linarith

/-- **Division-Free Lagrange Identity for Pairwise Sensor Disagreement**:
$$\sum_{i \in s} \sum_{j \in s} w_i w_j (y_i - y_j)^2
  = 2 \left(\sum_{i \in s} w_i\right) \left(\sum_{i \in s} w_i y_i^2\right)
    - 2 \left(\sum_{i \in s} w_i y_i\right)^2.$$ -/
theorem reconciliation_lagrange_pairwise_identity (s : Finset ι) (w y : ι → ℝ) :
    pairwiseDisagreementEnergy s w y =
      2 * totalPrecision s w * (∑ i ∈ s, w i * y i ^ 2) -
        2 * weightedMeasurementSum s w y ^ 2 := by
  unfold pairwiseDisagreementEnergy totalPrecision weightedMeasurementSum
  have hexpand : ∀ i ∈ s,
      (∑ j ∈ s, w i * w j * (y i - y j) ^ 2) =
        (w i * y i ^ 2) * (∑ j ∈ s, w j) -
          2 * (w i * y i) * (∑ j ∈ s, w j * y j) +
          w i * (∑ j ∈ s, w j * y j ^ 2) := by
    intro i _
    have hinner : ∀ j ∈ s,
        w i * w j * (y i - y j) ^ 2 =
          (w i * y i ^ 2) * w j - 2 * (w i * y i) * (w j * y j) + w i * (w j * y j ^ 2) := by
      intro j _
      ring
    rw [sum_congr rfl hinner, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  rw [sum_congr rfl hexpand, sum_add_distrib, sum_sub_distrib]
  rw [← sum_mul, ← sum_mul, ← mul_sum, ← sum_mul]
  ring

/-- **Pairwise Disagreement Identity (`reconciliation_disagreement_eq_pairwise`)**:
When $W = \sum_{i \in s} w_i \ne 0$, twice the total precision times the internal innovation
residual energy equals the all-pairs precision-weighted disagreement energy:
$$2 W \sum_{i \in s} w_i (y_i - \hat{x})^2
  = \sum_{i \in s} \sum_{j \in s} w_i w_j (y_i - y_j)^2.$$ -/
theorem reconciliation_disagreement_eq_pairwise (s : Finset ι) (w y : ι → ℝ)
    (hW : totalPrecision s w ≠ 0) :
    2 * totalPrecision s w * reconciliationResidualEnergy s w y (reconciledEstimate s w y) =
      pairwiseDisagreementEnergy s w y := by
  rw [reconciliation_lagrange_pairwise_identity]
  unfold reconciliationResidualEnergy reconciledEstimate
  set W := totalPrecision s w
  set S := weightedMeasurementSum s w y
  have hpoint : ∀ i ∈ s,
      w i * (y i - S / W) ^ 2 =
        w i * y i ^ 2 - 2 * (S / W) * (w i * y i) + w i * (S / W) ^ 2 := by
    intro i _
    ring
  rw [sum_congr rfl hpoint, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
  change 2 * W * ((∑ i ∈ s, w i * y i ^ 2) - 2 * (S / W) * S + W * (S / W) ^ 2) =
    2 * W * (∑ i ∈ s, w i * y i ^ 2) - 2 * S ^ 2
  field_simp [hW]
  ring

/-- **Exact Reconciliation Variance–Pairwise Identity**
(`reconciliation_variance_pairwise_identity`):
For any state $x \in \mathbb{R}$ and $W = \sum_{i \in s} w_i \ne 0$,
$$2 W \sum_{i \in s} w_i (y_i - x)^2
  = 2 W^2 (\hat{x} - x)^2 + \sum_{i \in s} \sum_{j \in s} w_i w_j (y_i - y_j)^2.$$ -/
theorem reconciliation_variance_pairwise_identity (s : Finset ι) (w y : ι → ℝ) (x : ℝ)
    (hW : totalPrecision s w ≠ 0) :
    2 * totalPrecision s w * reconciliationResidualEnergy s w y x =
      2 * totalPrecision s w ^ 2 * (reconciledEstimate s w y - x) ^ 2 +
        pairwiseDisagreementEnergy s w y := by
  rw [reconciliation_quadratic_completion s w y x hW, mul_add,
      reconciliation_disagreement_eq_pairwise s w y hW]
  ring

/-- Individual sensor pairwise disagreement score against an ensemble $s$:
$D_k(s) = \sum_{j \in s} w_j (y_k - y_j)^2$. -/
def sensorDisagreementScore (s : Finset ι) (w y : ι → ℝ) (k : ι) : ℝ :=
  ∑ j ∈ s, w j * (y k - y j) ^ 2

/-- **Healthy-Ensemble Pairwise Consistency Bound**:
If all sensors $i, j \in s_{\mathrm{healthy}}$ satisfy $|y_i - y_j| \le \varepsilon$ with
$w_j \ge 0$, then every healthy sensor $i \in s_{\mathrm{healthy}}$ has disagreement score
at most $W_{\mathrm{healthy}} \varepsilon^2$. -/
theorem healthy_sensor_disagreement_le (s_healthy : Finset ι) (w y : ι → ℝ) (ε : ℝ)
    (hw : ∀ j ∈ s_healthy, 0 ≤ w j) (hε : 0 ≤ ε)
    (hcons : ∀ i ∈ s_healthy, ∀ j ∈ s_healthy, |y i - y j| ≤ ε)
    {i : ι} (hi : i ∈ s_healthy) :
    sensorDisagreementScore s_healthy w y i ≤ totalPrecision s_healthy w * ε ^ 2 := by
  unfold sensorDisagreementScore totalPrecision
  rw [sum_mul]
  apply sum_le_sum
  intro j hj
  have hij : |y i - y j| ≤ ε := hcons i hi j hj
  have hsq : (y i - y j) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs (y i - y j)]
    exact sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg hε]; exact hij)
  exact mul_le_mul_of_nonneg_left hsq (hw j hj)

/-- **Faulty-Sensor Reconciliation Isolation Bound (`reconciliation_fault_isolation_bound`)**:
If all healthy sensors in $s_{\mathrm{healthy}}$ are pairwise $\varepsilon$-consistent
($|y_i - y_j| \le \varepsilon$) with threshold $\tau \ge W_{\mathrm{healthy}} \varepsilon^2$,
then any sensor $k$ whose disagreement score against $s_{\mathrm{healthy}}$ strictly exceeds $\tau$
cannot belong to $s_{\mathrm{healthy}}$ and strictly exceeds the score of every healthy sensor. -/
theorem reconciliation_fault_isolation_bound (s_healthy : Finset ι) (w y : ι → ℝ) (ε τ : ℝ)
    (hw : ∀ j ∈ s_healthy, 0 ≤ w j) (hε : 0 ≤ ε)
    (hcons : ∀ i ∈ s_healthy, ∀ j ∈ s_healthy, |y i - y j| ≤ ε)
    (hτ : totalPrecision s_healthy w * ε ^ 2 ≤ τ)
    {k : ι} (hfault : τ < sensorDisagreementScore s_healthy w y k) :
    k ∉ s_healthy ∧
      ∀ i ∈ s_healthy,
        sensorDisagreementScore s_healthy w y i < sensorDisagreementScore s_healthy w y k := by
  refine ⟨?_, ?_⟩
  · intro hk
    have hle := healthy_sensor_disagreement_le s_healthy w y ε hw hε hcons hk
    linarith
  · intro i hi
    have hle := healthy_sensor_disagreement_le s_healthy w y ε hw hε hcons hi
    linarith

/-- Staleness-inflated effective precision $w(\Delta t) = (\sigma^2 + \sigma_a^2 \Delta t^2)^{-1}$
for base measurement variance $\sigma^2 > 0$, acceleration drift variance rate $\sigma_a^2 \ge 0$,
and measurement age $\Delta t \ge 0$. -/
noncomputable def effectivePrecision (σ_sq σ_a_sq Δt : ℝ) : ℝ :=
  1 / (σ_sq + σ_a_sq * Δt ^ 2)

/-- **Staleness-Inflated Precision Monotonicity (`staleness_inflated_precision_mono`)**:
For $\sigma^2 > 0$, $\sigma_a^2 \ge 0$, and $0 \le \Delta t_1 \le \Delta t_2$, aging a measurement
monotonically decreases its optimal reconciliation precision while keeping it strictly positive
and bounded above by $\sigma^{-2}$. -/
theorem staleness_inflated_precision_mono {σ_sq σ_a_sq Δt₁ Δt₂ : ℝ}
    (hσ : 0 < σ_sq) (hσa : 0 ≤ σ_a_sq) (ht₁ : 0 ≤ Δt₁) (ht₁₂ : Δt₁ ≤ Δt₂) :
    0 < effectivePrecision σ_sq σ_a_sq Δt₂ ∧
      effectivePrecision σ_sq σ_a_sq Δt₂ ≤ effectivePrecision σ_sq σ_a_sq Δt₁ ∧
      effectivePrecision σ_sq σ_a_sq Δt₁ ≤ 1 / σ_sq := by
  unfold effectivePrecision
  have hsq : Δt₁ ^ 2 ≤ Δt₂ ^ 2 := by nlinarith
  have hden1 : 0 < σ_sq + σ_a_sq * Δt₁ ^ 2 := by positivity
  have hden2 : 0 < σ_sq + σ_a_sq * Δt₂ ^ 2 := by positivity
  have hle12 : σ_sq + σ_a_sq * Δt₁ ^ 2 ≤ σ_sq + σ_a_sq * Δt₂ ^ 2 := by
    linarith [mul_le_mul_of_nonneg_left hsq hσa]
  have hle01 : σ_sq ≤ σ_sq + σ_a_sq * Δt₁ ^ 2 := by
    linarith [mul_nonneg hσa (sq_nonneg Δt₁)]
  refine ⟨by positivity, ?_, ?_⟩
  · exact one_div_le_one_div_of_le hden1 hle12
  · exact one_div_le_one_div_of_le hσ hle01

/-- **Strict Precision Decay Under Positive Drift Rate**:
When $\sigma^2 > 0$, $\sigma_a^2 > 0$, and $0 \le \Delta t_1 < \Delta t_2$, older measurements
receive strictly smaller precision weight. -/
theorem staleness_inflated_precision_strict_anti {σ_sq σ_a_sq Δt₁ Δt₂ : ℝ}
    (hσ : 0 < σ_sq) (hσa : 0 < σ_a_sq) (ht₁ : 0 ≤ Δt₁) (ht₁₂ : Δt₁ < Δt₂) :
    effectivePrecision σ_sq σ_a_sq Δt₂ < effectivePrecision σ_sq σ_a_sq Δt₁ := by
  unfold effectivePrecision
  have hsq : Δt₁ ^ 2 < Δt₂ ^ 2 := by nlinarith
  have hden1 : 0 < σ_sq + σ_a_sq * Δt₁ ^ 2 := by positivity
  have hlt12 : σ_sq + σ_a_sq * Δt₁ ^ 2 < σ_sq + σ_a_sq * Δt₂ ^ 2 := by
    linarith [mul_lt_mul_of_pos_left hsq hσa]
  exact one_div_lt_one_div_of_lt hden1 hlt12

/-! ## 3. Orchestration of Control (Multi-Rate Cascade, Simplex Authority & Pseudo-Huber) -/

/-- Scalar CBF safety-blended command
$u_{\mathrm{cbf}} = (1 - \lambda) u_{\mathrm{nom}} + \lambda u_{\mathrm{brake}}$. -/
def cbfBlendCommand (u_nom u_brake lam : ℝ) : ℝ :=
  (1 - lam) * u_nom + lam * u_brake

/-- 3-Tier scalar orchestrated command: selects `cbfBlendCommand` when the timing/reconciliation
guard `g_ok` holds, and switches to emergency fallback `u_brake` otherwise. -/
def orchestratedCommand (g_ok : Bool) (u_nom u_brake lam : ℝ) : ℝ :=
  if g_ok then cbfBlendCommand u_nom u_brake lam else u_brake

/-- Vector CBF safety-blended command
$u_{\mathrm{cbf}} = (1 - \lambda) u_{\mathrm{nom}} + \lambda u_{\mathrm{brake}}$. -/
def cbfBlendVec {n : Type*} (u_nom u_brake : n → ℝ) (lam : ℝ) : n → ℝ :=
  fun i => (1 - lam) * u_nom i + lam * u_brake i

/-- 3-Tier vector orchestrated command across nominal, CBF-intervening, and Simplex
fallback modes. -/
def orchestratedVec {n : Type*} (g_ok : Bool) (u_nom u_brake : n → ℝ) (lam : ℝ) : n → ℝ :=
  if g_ok then cbfBlendVec u_nom u_brake lam else u_brake

/-- **Box Saturation Invariance of the 3-Tier Orchestrator**:
If $u_{\mathrm{nom}}, u_{\mathrm{brake}} \in [-U, U]$ and $\lambda \in [0, 1]$, then the
orchestrated command lies in $[-U, U]$ for every guard state `g_ok`. -/
theorem orchestrator_box_invariance (g_ok : Bool) {u_nom u_brake lam U : ℝ}
    (hnom : -U ≤ u_nom ∧ u_nom ≤ U) (hbrake : -U ≤ u_brake ∧ u_brake ≤ U)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    -U ≤ orchestratedCommand g_ok u_nom u_brake lam ∧
      orchestratedCommand g_ok u_nom u_brake lam ≤ U := by
  unfold orchestratedCommand cbfBlendCommand
  cases g_ok
  · exact hbrake
  · simp only [ ↓reduceIte]
    have h1lam : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
    constructor
    · nlinarith [hnom.1, hbrake.1]
    · nlinarith [hnom.2, hbrake.2]

/-- **Convex-Set Admissibility Invariance (`orchestrator_convex_hull_invariance`)**:
For any control set $C$ closed under convex combinations, if $u_{\mathrm{nom}} \in C$ and
$u_{\mathrm{brake}} \in C$, then `orchestratedVec g_ok u_nom u_brake lam ∈ C` across all guard
states `g_ok` and blend weights $\lambda \in [0, 1]$. -/
theorem orchestrator_convex_hull_invariance {n : Type*} (C : Set (n → ℝ))
    (hconv : ∀ u v : n → ℝ, u ∈ C → v ∈ C → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      cbfBlendVec u v lam ∈ C)
    (g_ok : Bool) {u_nom u_brake : n → ℝ} {lam : ℝ}
    (hnom : u_nom ∈ C) (hbrake : u_brake ∈ C) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    orchestratedVec g_ok u_nom u_brake lam ∈ C := by
  unfold orchestratedVec
  cases g_ok
  · exact hbrake
  · exact hconv u_nom u_brake hnom hbrake lam hlam0 hlam1

/-- **Safety Barrier Margin Monotonicity (`orchestrator_safety_margin_monotonicity`)**:
For any barrier normal vector $a \in \mathbb{R}^n$ and blend factor $\lambda \in [0, 1]$, if the
backup brake command has at least the barrier inner product of the nominal command
($a \cdot u_{\mathrm{nom}} \le a \cdot u_{\mathrm{brake}}$), then the CBF-blended and orchestrated
commands monotonically interpolate the safety margin:
$$a \cdot u_{\mathrm{nom}} \le a \cdot u_{\mathrm{cbf}}(\lambda)
  \le a \cdot u_{\mathrm{orch}}(g_{\mathrm{ok}}, \lambda) \le a \cdot u_{\mathrm{brake}}.$$ -/
theorem orchestrator_safety_margin_monotonicity {n : Type*} [Fintype n]
    (a u_nom u_brake : n → ℝ) (g_ok : Bool) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hmargin : a ⬝ᵥ u_nom ≤ a ⬝ᵥ u_brake) :
    a ⬝ᵥ u_nom ≤ a ⬝ᵥ cbfBlendVec u_nom u_brake lam ∧
      a ⬝ᵥ cbfBlendVec u_nom u_brake lam ≤ a ⬝ᵥ orchestratedVec g_ok u_nom u_brake lam ∧
      a ⬝ᵥ orchestratedVec g_ok u_nom u_brake lam ≤ a ⬝ᵥ u_brake := by
  have hdot : a ⬝ᵥ cbfBlendVec u_nom u_brake lam =
      (1 - lam) * (a ⬝ᵥ u_nom) + lam * (a ⬝ᵥ u_brake) := by
    unfold dotProduct cbfBlendVec
    have hpt : ∀ i ∈ (univ : Finset n),
        a i * ((1 - lam) * u_nom i + lam * u_brake i) =
          (1 - lam) * (a i * u_nom i) + lam * (a i * u_brake i) := by
      intro i _
      ring
    rw [sum_congr rfl hpt, sum_add_distrib, ← mul_sum, ← mul_sum]
  have h1lam : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have h_low : a ⬝ᵥ u_nom ≤ a ⬝ᵥ cbfBlendVec u_nom u_brake lam := by
    rw [hdot]; nlinarith
  have h_high : a ⬝ᵥ cbfBlendVec u_nom u_brake lam ≤ a ⬝ᵥ u_brake := by
    rw [hdot]; nlinarith
  refine ⟨h_low, ?_, ?_⟩
  · unfold orchestratedVec
    cases g_ok
    · exact h_high
    · exact le_rfl
  · unfold orchestratedVec
    cases g_ok
    · exact le_rfl
    · exact h_high

/-- Geometric series telescoping identity $(1 - \rho) \sum_{k=0}^{N-1} \rho^k = 1 - \rho^N$. -/
theorem one_sub_mul_geom_sum (ρ : ℝ) (N : ℕ) :
    (1 - ρ) * (∑ k ∈ range N, ρ ^ k) = 1 - ρ ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- **Multi-Rate Inner-Loop Telescoping Bound (`multi_rate_cascade_step_bound`)**:
If a fast inner loop satisfies $e(k + 1) \le \rho_{\mathrm{in}} e(k) + d_{\mathrm{out}}$ with
$\rho_{\mathrm{in}} \ge 0$ under a ZOH outer-loop staleness disturbance $d_{\mathrm{out}}$, then
after $N$ inner steps:
$$e(N) \le \rho_{\mathrm{in}}^N e(0)
  + \left(\sum_{k=0}^{N-1} \rho_{\mathrm{in}}^k\right) d_{\mathrm{out}}.$$ -/
theorem multi_rate_cascade_step_bound (e : ℕ → ℝ) (ρ_in d_out : ℝ)
    (hρ : 0 ≤ ρ_in)
    (hstep : ∀ k : ℕ, e (k + 1) ≤ ρ_in * e k + d_out) (N : ℕ) :
    e N ≤ ρ_in ^ N * e 0 + (∑ k ∈ range N, ρ_in ^ k) * d_out := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := hstep N
    have hmul : ρ_in * e N ≤ ρ_in * (ρ_in ^ N * e 0 + (∑ k ∈ range N, ρ_in ^ k) * d_out) :=
      mul_le_mul_of_nonneg_left ih hρ
    have hgeom : ∑ k ∈ range (N + 1), ρ_in ^ k = 1 + ρ_in * ∑ k ∈ range N, ρ_in ^ k := by
      rw [sum_range_succ', pow_zero, mul_sum]
      simp_rw [pow_succ']
      ring
    rw [hgeom, pow_succ']
    linarith

/-- **Multi-Rate Cascade Input-to-State Stability Bound (`multi_rate_cascade_iss_bound`)**:
When the fast inner loop contracts with factor $\rho_{\mathrm{in}} \in [0, 1)$ per inner step and
the slow outer perception/planning loop updates every $N$ inner steps with staleness disturbance
$d_{\mathrm{out}}$, the $N$-step composed orchestration map satisfies
$$e(N) \le \rho_{\mathrm{in}}^N e(0)
  + \frac{1 - \rho_{\mathrm{in}}^N}{1 - \rho_{\mathrm{in}}} d_{\mathrm{out}}.$$ -/
theorem multi_rate_cascade_iss_bound (e : ℕ → ℝ) (ρ_in d_out : ℝ)
    (hρ0 : 0 ≤ ρ_in) (hρ1 : ρ_in < 1)
    (hstep : ∀ k : ℕ, e (k + 1) ≤ ρ_in * e k + d_out) (N : ℕ) :
    e N ≤ ρ_in ^ N * e 0 + (1 - ρ_in ^ N) / (1 - ρ_in) * d_out := by
  have hbase := multi_rate_cascade_step_bound e ρ_in d_out hρ0 hstep N
  have h1ρ : 1 - ρ_in ≠ 0 := sub_ne_zero.mpr hρ1.ne'
  have hsum : (∑ k ∈ range N, ρ_in ^ k) = (1 - ρ_in ^ N) / (1 - ρ_in) := by
    rw [eq_div_iff h1ρ, mul_comm]
    exact one_sub_mul_geom_sum ρ_in N
  rwa [hsum] at hbase

/-- **Multi-Rate Cascade Sublevel Invariance**:
If $\rho_{\mathrm{in}} \in [0, 1)$, $d_{\mathrm{out}} \ge 0$, and the initial inner error lies in
the asymptotic ISS ball $e(0) \le \frac{d_{\mathrm{out}}}{1 - \rho_{\mathrm{in}}}$, then $e(N)$
remains inside $\frac{d_{\mathrm{out}}}{1 - \rho_{\mathrm{in}}}$ for every multi-rate ratio $N$. -/
theorem multi_rate_cascade_sublevel_invariant (e : ℕ → ℝ) (ρ_in d_out : ℝ)
    (hρ0 : 0 ≤ ρ_in) (hρ1 : ρ_in < 1)
    (hstep : ∀ k : ℕ, e (k + 1) ≤ ρ_in * e k + d_out)
    (he0 : e 0 ≤ d_out / (1 - ρ_in)) (N : ℕ) :
    e N ≤ d_out / (1 - ρ_in) := by
  have hiss := multi_rate_cascade_iss_bound e ρ_in d_out hρ0 hρ1 hstep N
  have hpow : 0 ≤ ρ_in ^ N := pow_nonneg hρ0 N
  have h1ρ : 0 < 1 - ρ_in := sub_pos.mpr hρ1
  have hmul : ρ_in ^ N * e 0 ≤ ρ_in ^ N * (d_out / (1 - ρ_in)) :=
    mul_le_mul_of_nonneg_left he0 hpow
  have hident : ρ_in ^ N * (d_out / (1 - ρ_in)) + (1 - ρ_in ^ N) / (1 - ρ_in) * d_out =
      d_out / (1 - ρ_in) := by
    field_simp [h1ρ.ne']
    ring
  linarith

/-- Smooth Pseudo-Huber penalty $\phi_\varepsilon(x) = \sqrt{x^2 + \varepsilon^2} - \varepsilon$. -/
noncomputable def pseudoHuber (ε x : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + ε ^ 2) - ε

/-- **Exact Quadratic Identity for Pseudo-Huber**:
$(\phi_\varepsilon(x) + \varepsilon)^2 = x^2 + \varepsilon^2$. -/
theorem pseudoHuber_add_eps_sq (ε x : ℝ) :
    (pseudoHuber ε x + ε) ^ 2 = x ^ 2 + ε ^ 2 := by
  unfold pseudoHuber
  rw [sub_add_cancel]
  exact Real.sq_sqrt (by positivity)

/-- **Nonnegativity of Pseudo-Huber**:
For $\varepsilon \ge 0$, $0 \le \phi_\varepsilon(x)$. -/
theorem pseudoHuber_nonneg {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ pseudoHuber ε x := by
  unfold pseudoHuber
  rw [sub_nonneg]
  have hle : ε ^ 2 ≤ x ^ 2 + ε ^ 2 := by linarith [sq_nonneg x]
  calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
    _ ≤ Real.sqrt (x ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt hle

/-- **Linear Upper Envelope of Pseudo-Huber**:
For $\varepsilon \ge 0$, $\phi_\varepsilon(x) \le |x|$. -/
theorem pseudoHuber_le_abs {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    pseudoHuber ε x ≤ |x| := by
  unfold pseudoHuber
  rw [sub_le_iff_le_add]
  have hle : x ^ 2 + ε ^ 2 ≤ (|x| + ε) ^ 2 := by
    have : 0 ≤ 2 * |x| * ε := by positivity
    calc x ^ 2 + ε ^ 2 = |x| ^ 2 + ε ^ 2 := by rw [sq_abs]
      _ ≤ |x| ^ 2 + 2 * |x| * ε + ε ^ 2 := by linarith
      _ = (|x| + ε) ^ 2 := by ring
  calc Real.sqrt (x ^ 2 + ε ^ 2)
      ≤ Real.sqrt ((|x| + ε) ^ 2) := Real.sqrt_le_sqrt hle
    _ = |x| + ε := Real.sqrt_sq (by positivity)

/-- **Strict Linear Lower Envelope of Pseudo-Huber**:
For $\varepsilon > 0$, $|x| - \varepsilon < \phi_\varepsilon(x)$. -/
theorem abs_sub_eps_lt_pseudoHuber {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |x| - ε < pseudoHuber ε x := by
  unfold pseudoHuber
  rw [sub_lt_sub_iff_right]
  have hlt : |x| ^ 2 < x ^ 2 + ε ^ 2 := by
    rw [sq_abs]
    linarith [sq_pos_of_pos hε]
  calc |x| = Real.sqrt (|x| ^ 2) := (Real.sqrt_sq (abs_nonneg x)).symm
    _ < Real.sqrt (x ^ 2 + ε ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg |x|) hlt

/-- **Quadratic Upper Bound of Pseudo-Huber**:
For $\varepsilon > 0$, $\phi_\varepsilon(x) \le \frac{x^2}{2\varepsilon}$. -/
theorem pseudoHuber_le_quadratic_half {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    pseudoHuber ε x ≤ x ^ 2 / (2 * ε) := by
  unfold pseudoHuber
  rw [sub_le_iff_le_add]
  have hle : x ^ 2 + ε ^ 2 ≤ (x ^ 2 / (2 * ε) + ε) ^ 2 := by
    have h2e : 2 * ε ≠ 0 := mul_ne_zero two_ne_zero hε.ne'
    have hsq : 0 ≤ (x ^ 2 / (2 * ε)) ^ 2 := sq_nonneg _
    have hexp : (x ^ 2 / (2 * ε) + ε) ^ 2 =
        x ^ 2 + ε ^ 2 + (x ^ 2 / (2 * ε)) ^ 2 := by
      field_simp [h2e]
      ring
    linarith
  calc Real.sqrt (x ^ 2 + ε ^ 2)
      ≤ Real.sqrt ((x ^ 2 / (2 * ε) + ε) ^ 2) := Real.sqrt_le_sqrt hle
    _ = x ^ 2 / (2 * ε) + ε := Real.sqrt_sq (by positivity)

/-- **Master Pseudo-Huber Envelope Certificate (`pseudo_huber_bounds_and_lipschitz`)**:
For $\varepsilon > 0$ and all $x \in \mathbb{R}$,
$0 \le \phi_\varepsilon(x) \le |x|$, $|x| - \varepsilon < \phi_\varepsilon(x)$, and
$\phi_\varepsilon(x) \le \frac{x^2}{2\varepsilon}$. -/
theorem pseudo_huber_bounds_and_lipschitz {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ pseudoHuber ε x ∧
      pseudoHuber ε x ≤ |x| ∧
      |x| - ε < pseudoHuber ε x ∧
      pseudoHuber ε x ≤ x ^ 2 / (2 * ε) :=
  ⟨pseudoHuber_nonneg hε.le x,
   pseudoHuber_le_abs hε.le x,
   abs_sub_eps_lt_pseudoHuber hε x,
   pseudoHuber_le_quadratic_half hε x⟩

end ControlsLean.Controls
