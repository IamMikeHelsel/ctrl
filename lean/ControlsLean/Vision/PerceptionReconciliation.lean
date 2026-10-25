/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Vision.Epipolar
import ControlsLean.Vision.Triangulation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Machine Vision & Perception Under Motion, Outliers & Persistent-Excitation Gates

This module formalizes three foundational pillars of safety-critical visual perception and
online sensor calibration:

1. **Rolling-Shutter & Velocity-Induced Epipolar / Cheirality Bias**:
   - `motionShiftedTranslation`, `epipolarResidual`, `epipolar_motion_shift_identity`:
     Exact perturbation of the essential matrix action $E(\tilde{t}) x_1$ and Longuet-Higgins
     epipolar residual $x_2^\top E x_1$ under camera velocity $v$ and scanline/timestamp skew
     $\delta t$.
   - `epipolar_motion_bias_identity`, `epipolar_motion_bias_bound`:
     Along a motion-skewed scene ray $d_2 x_2 = R (d_1 x_1) + t - \delta t \, v$, the nominal
     epipolar residual equals $-\frac{\delta t}{d_2} v \cdot (t \times R x_1)$, vanishing if and
     only if velocity $v$ lies in the epipolar plane $\operatorname{span}(t, R x_1)$.
   - `triangulationDepth1Numer`, `triangulationDepth1Numer_motion_shift`,
     `cheirality_sign_invariant_of_motion_margin`: Exact motion-perturbation identity for the
     two-view triangulation depth numerator and the margin condition under which positive
     cheirality depth $d_1 > 0$ is invariant to timestamp skew $\delta t$.

2. **Certifiable Outlier-Robust Perception (Truncated Least Squares / GNC Duality)**:
   - `tlsSurrogateTerm`, `tlsTruncatedTerm`, `tlsOptimalWeight`,
     `tlsDualObjective`, `tlsPrimalObjective`: Black–Rangarajan / Graduated Non-Convexity (GNC)
     convex-with-weights surrogate for Truncated Least Squares (TLS).
   - `tlsSurrogateTerm_sub_truncated_eq`, `tls_truncated_le_surrogate`,
     `tls_optimal_weight_one_of_inlier`, `tls_optimal_weight_zero_of_outlier`,
     `tls_surrogate_at_optimal_weight`: Pointwise exactness of binary weight selection
     $w_i^\star \in \{0, 1\}$ separating inliers ($r_i^2 \le \bar{c}^2$) from outliers
     ($r_i^2 > \bar{c}^2$).
   - `tls_dual_weight_identity`, `tls_objective_le_unweighted`: Ensemble-level duality
     $\min_{w_i \in [0, 1]} \sum_{i \in s} (w_i r_i^2 + \bar{c}^2 (1 - w_i))
       = \sum_{i \in s} \min(r_i^2, \bar{c}^2)$
     and uniform outlier influence clamping $\le |s| \bar{c}^2$.

3. **Effective-Rank Persistent Excitation Gate for Online Calibration (`paramsd`)**:
   - `gram2Matrix`, `gram2Trace`, `gram2Det`, `gram2FrobSq`,
     `trace_gram2Matrix`, `det_gram2Matrix`, `trace_sq_gram2Matrix`:
     $2 \times 2$ symmetric regressor Gram matrix $G = \begin{bmatrix} a & b \\ b & d \end{bmatrix}$
     invariants $\operatorname{tr}(G)$, $\det(G)$, and $\operatorname{tr}(G^2) = \|G\|_F^2$.
   - `gram2_trace_sq_sub_trace_sq_eq_two_det`, `gram2_two_frobSq_sub_trace_sq_eq_sum_sq`,
     `gram2_trace_sq_bounds`: Exact eigenvalue-free polynomial identities
     $(\operatorname{tr} G)^2 - \operatorname{tr}(G^2) = 2 \det(G)$ and
     $2 \operatorname{tr}(G^2) - (\operatorname{tr} G)^2 = (a - d)^2 + 4 b^2$, yielding the tight
     effective-rank sandwich
     $\operatorname{tr}(G^2) \le (\operatorname{tr} G)^2 \le 2 \operatorname{tr}(G^2)$.
   - `gram2_det_pos_of_effRank_gt_one`, `gram2_schur_completion_of_squares`,
     `gram2_posDef_of_trace_pos_effRank_gt_one`: Division-free and SVD-free persistent excitation
     certificate proving that
     $r_{\mathrm{eff}}(G) = (\operatorname{tr} G)^2 / \operatorname{tr}(G^2) > 1$
     is strictly equivalent to $\det(G) > 0$.
-/

namespace ControlsLean.Vision

open Finset Matrix

/-! ## 1. Rolling-Shutter & Velocity-Induced Epipolar / Cheirality Bias -/

/-- Apparent baseline translation $\tilde{t}(\delta t) = t - \delta t \cdot v$ under camera
linear velocity $v$ and scanline/timestamp delay $\delta t$. -/
def motionShiftedTranslation (t v : Fin 3 → ℝ) (δt : ℝ) : Fin 3 → ℝ :=
  t - δt • v

/-- Longuet-Higgins epipolar residual
$x_2^\top E x_1 = x_2 \cdot (\mathrm{essential}\ R\ t *ᵥ x_1)$. -/
noncomputable def epipolarResidual (R : Matrix (Fin 3) (Fin 3) ℝ) (t x₁ x₂ : Fin 3 → ℝ) : ℝ :=
  x₂ ⬝ᵥ (essential R t *ᵥ x₁)

/-- **Epipolar Residual Decomposition Under Baseline Velocity Shift**:
Replacing $t$ by $t - \delta t \cdot v$ perturbs the Longuet-Higgins residual by the exact
bilinear cross-product term $-\delta t \, (x_2 \cdot (v \times R x_1))$. -/
theorem epipolar_motion_shift_identity
    (R : Matrix (Fin 3) (Fin 3) ℝ) (t v x₁ x₂ : Fin 3 → ℝ) (δt : ℝ) :
    epipolarResidual R (motionShiftedTranslation t v δt) x₁ x₂ =
      epipolarResidual R t x₁ x₂ - δt * (x₂ ⬝ᵥ (v ⨯₃ (R *ᵥ x₁))) := by
  unfold epipolarResidual motionShiftedTranslation
  rw [essential_mulVec, essential_mulVec]
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- **Motion-Biased Epipolar Residual Identity (`epipolar_motion_bias_identity`)**:
If a scene point observed under rolling-shutter / timestamp delay $\delta t$ satisfies the
motion-shifted camera equation $d_2 x_2 = R (d_1 x_1) + t - \delta t \cdot v$, then:
1. $d_2 \, (x_2 \cdot (E x_1)) = -\delta t \, (v \cdot (t \times R x_1))$.
2. When $d_2 \ne 0$, $x_2 \cdot (E x_1) = -\frac{\delta t}{d_2} (v \cdot (t \times R x_1))$. -/
theorem epipolar_motion_bias_identity
    (R : Matrix (Fin 3) (Fin 3) ℝ) (t v x₁ x₂ : Fin 3 → ℝ) (d₁ d₂ δt : ℝ)
    (hscene : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t - δt • v) :
    d₂ * epipolarResidual R t x₁ x₂ = -δt * (v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))) ∧
      (d₂ ≠ 0 → epipolarResidual R t x₁ x₂ = -(δt / d₂) * (v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁)))) := by
  have hscaled : d₂ * epipolarResidual R t x₁ x₂ = -δt * (v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))) := by
    unfold epipolarResidual
    rw [essential_mulVec, ← smul_eq_mul, ← smul_dotProduct, hscene]
    rw [mulVec_smul, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
    rw [dot_cross_self, dot_self_cross]
    simp [smul_eq_mul]
  refine ⟨hscaled, fun hd₂ => ?_⟩
  calc epipolarResidual R t x₁ x₂
      = (d₂ * epipolarResidual R t x₁ x₂) / d₂ := by field_simp [hd₂]
    _ = (-δt * (v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁)))) / d₂ := by rw [hscaled]
    _ = -(δt / d₂) * (v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))) := by ring

/-- **Motion-Biased Epipolar Residual Magnitude Bound (`epipolar_motion_bias_bound`)**:
If a motion-skewed correspondence satisfies $d_2 x_2 = R (d_1 x_1) + t - \delta t \cdot v$ with
depth $d_2 \ge d_{\min} > 0$, timestamp skew $|\delta t| \le \tau_{\max}$, and coplanarity triple
product $|v \cdot (t \times R x_1)| \le B$, then the nominal epipolar residual is bounded by
$$|x_2^\top E x_1| \le \frac{\tau_{\max} B}{d_{\min}}.$$ -/
theorem epipolar_motion_bias_bound
    (R : Matrix (Fin 3) (Fin 3) ℝ) (t v x₁ x₂ : Fin 3 → ℝ)
    {d₁ d₂ δt d_min τ_max B : ℝ}
    (hscene : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t - δt • v)
    (hd_min : 0 < d_min) (hd₂ : d_min ≤ d₂)
    (hτ : |δt| ≤ τ_max) (hB : |v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))| ≤ B) :
    |epipolarResidual R t x₁ x₂| ≤ τ_max * B / d_min := by
  have hd₂_pos : 0 < d₂ := lt_of_lt_of_le hd_min hd₂
  have hscaled := (epipolar_motion_bias_identity R t v x₁ x₂ d₁ d₂ δt hscene).1
  have habs : d₂ * |epipolarResidual R t x₁ x₂| =
      |δt| * |v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))| := by
    calc d₂ * |epipolarResidual R t x₁ x₂|
        = |d₂ * epipolarResidual R t x₁ x₂| := by
          rw [abs_mul, abs_of_pos hd₂_pos]
      _ = |-δt * (v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁)))| := by rw [hscaled]
      _ = |δt| * |v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))| := by rw [abs_mul, abs_neg]
  have hτ_nonneg : 0 ≤ τ_max := (abs_nonneg δt).trans hτ
  have hB_nonneg : 0 ≤ B := (abs_nonneg _).trans hB
  have hprod : |δt| * |v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))| ≤ τ_max * B :=
    mul_le_mul hτ hB (abs_nonneg _) hτ_nonneg
  rw [le_div_iff₀ hd_min]
  calc |epipolarResidual R t x₁ x₂| * d_min
      ≤ |epipolarResidual R t x₁ x₂| * d₂ :=
        mul_le_mul_of_nonneg_left hd₂ (abs_nonneg _)
    _ = d₂ * |epipolarResidual R t x₁ x₂| := mul_comm _ _
    _ = |δt| * |v ⬝ᵥ (t ⨯₃ (R *ᵥ x₁))| := habs
    _ ≤ τ_max * B := hprod

/-- Cleared-denominator numerator $N_1(t) = -((x_2 \times R x_1) \cdot (x_2 \times t))$ of the
closed-form triangulated depth $d_1 = N_1(t) / \|x_2 \times R x_1\|^2$. -/
def triangulationDepth1Numer (R : Matrix (Fin 3) (Fin 3) ℝ) (t x₁ x₂ : Fin 3 → ℝ) : ℝ :=
  -((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ t))

/-- **Linear Perturbation of the Triangulated Depth Numerator Under Motion Skew**:
$N_1(t - \delta t \cdot v) = N_1(t) - \delta t \, N_1(v)$. -/
theorem triangulationDepth1Numer_motion_shift
    (R : Matrix (Fin 3) (Fin 3) ℝ) (t v x₁ x₂ : Fin 3 → ℝ) (δt : ℝ) :
    triangulationDepth1Numer R (motionShiftedTranslation t v δt) x₁ x₂ =
      triangulationDepth1Numer R t x₁ x₂ - δt * triangulationDepth1Numer R v x₁ x₂ := by
  unfold triangulationDepth1Numer motionShiftedTranslation
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- **Cheirality Sign Invariance Under Motion Margin**
(`cheirality_sign_invariant_of_motion_margin`):
If a scene point has positive nominal depth numerator $N_1(t) > 0$ and the velocity-induced
timestamp perturbation satisfies $|\delta t| \cdot |N_1(v)| < N_1(t)$, then the motion-perturbed
triangulated depth $\tilde{d}_1$ satisfies $\tilde{d}_1 > 0$ (preserving front-of-camera
cheirality). -/
theorem cheirality_sign_invariant_of_motion_margin
    (R : Matrix (Fin 3) (Fin 3) ℝ) (t v x₁ x₂ : Fin 3 → ℝ) (δt d₁_tilde d₂_tilde : ℝ)
    (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0)
    (hscene : d₂_tilde • x₂ = R *ᵥ (d₁_tilde • x₁) + motionShiftedTranslation t v δt)
    (hmargin : |δt * triangulationDepth1Numer R v x₁ x₂| < triangulationDepth1Numer R t x₁ x₂) :
    0 < d₁_tilde := by
  have hd1 := depth₁_eq hn hscene
  have hnum_pos : 0 < triangulationDepth1Numer R (motionShiftedTranslation t v δt) x₁ x₂ := by
    rw [triangulationDepth1Numer_motion_shift]
    have hle := le_abs_self (δt * triangulationDepth1Numer R v x₁ x₂)
    linarith
  have hden_nonneg : 0 ≤ (x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hden_ne : (x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)) ≠ 0 :=
    fun h => hn (dotProduct_self_eq_zero.mp h)
  have hden_pos : 0 < (x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)) :=
    lt_of_le_of_ne hden_nonneg hden_ne.symm
  rw [hd1]
  exact div_pos hnum_pos hden_pos

/-! ## 2. Certifiable Outlier-Robust Perception (Truncated Least Squares / GNC Duality) -/

variable {ι : Type*}

/-- Single-correspondence Black–Rangarajan / GNC dual TLS surrogate term
$L_{\mathrm{TLS}}(r, w; \bar{c}) = w r^2 + \bar{c}^2 (1 - w)$. -/
def tlsSurrogateTerm (c r w : ℝ) : ℝ :=
  w * r ^ 2 + c ^ 2 * (1 - w)

/-- Primal truncated least squares (TLS) residual cost $\min(r^2, \bar{c}^2)$. -/
def tlsTruncatedTerm (c r : ℝ) : ℝ :=
  min (r ^ 2) (c ^ 2)

/-- Optimal GNC binary inlier/outlier weight $w^\star(r; \bar{c}) \in \{0, 1\}$. -/
noncomputable def tlsOptimalWeight (c r : ℝ) : ℝ :=
  if r ^ 2 ≤ c ^ 2 then 1 else 0

/-- Ensemble-level GNC dual TLS objective $\sum_{i \in s} (w_i r_i^2 + \bar{c}^2 (1 - w_i))$. -/
def tlsDualObjective (s : Finset ι) (c : ℝ) (r w : ι → ℝ) : ℝ :=
  ∑ i ∈ s, tlsSurrogateTerm c (r i) (w i)

/-- Ensemble-level primal TLS objective $\sum_{i \in s} \min(r_i^2, \bar{c}^2)$. -/
def tlsPrimalObjective (s : Finset ι) (c : ℝ) (r : ι → ℝ) : ℝ :=
  ∑ i ∈ s, tlsTruncatedTerm c (r i)

/-- **Exact Pointwise Gap Between GNC Surrogate and Truncated Least Squares**:
$$w r^2 + \bar{c}^2 (1 - w) - \min(r^2, \bar{c}^2) =
  \begin{cases}
    (1 - w)(\bar{c}^2 - r^2) & \text{if } r^2 \le \bar{c}^2, \\
    w (r^2 - \bar{c}^2) & \text{if } r^2 > \bar{c}^2.
  \end{cases}$$ -/
theorem tlsSurrogateTerm_sub_truncated_eq (c r w : ℝ) :
    tlsSurrogateTerm c r w - tlsTruncatedTerm c r =
      if r ^ 2 ≤ c ^ 2 then (1 - w) * (c ^ 2 - r ^ 2) else w * (r ^ 2 - c ^ 2) := by
  unfold tlsSurrogateTerm tlsTruncatedTerm
  split_ifs with h
  · rw [min_eq_left h]
    ring
  · rw [min_eq_right (le_of_not_ge h)]
    ring

/-- **Pointwise Lower Bound of the GNC Surrogate**:
For every weight $w \in [0, 1]$, $\min(r^2, \bar{c}^2) \le w r^2 + \bar{c}^2 (1 - w)$. -/
theorem tls_truncated_le_surrogate (c r : ℝ) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    tlsTruncatedTerm c r ≤ tlsSurrogateTerm c r w := by
  rw [← sub_nonneg, tlsSurrogateTerm_sub_truncated_eq]
  split_ifs with h
  · exact mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr h)
  · have hgt : c ^ 2 < r ^ 2 := lt_of_not_ge h
    exact mul_nonneg hw0 (sub_nonneg.mpr hgt.le)

/-- Optimal TLS weight always lies in $[0, 1]$. -/
theorem tls_optimal_weight_in_unit_interval (c r : ℝ) :
    0 ≤ tlsOptimalWeight c r ∧ tlsOptimalWeight c r ≤ 1 := by
  unfold tlsOptimalWeight
  split_ifs <;> constructor <;> norm_num

/-- **Inlier Weight Selection (`tls_optimal_weight_one_of_inlier`)**:
When $r^2 \le \bar{c}^2$, the optimal GNC weight is $w^\star = 1$. -/
theorem tls_optimal_weight_one_of_inlier {c r : ℝ} (hin : r ^ 2 ≤ c ^ 2) :
    tlsOptimalWeight c r = 1 := by
  simp [tlsOptimalWeight, hin]

/-- **Outlier Weight Rejection (`tls_optimal_weight_zero_of_outlier`)**:
When $r^2 > \bar{c}^2$, the optimal GNC weight is $w^\star = 0$. -/
theorem tls_optimal_weight_zero_of_outlier {c r : ℝ} (hout : c ^ 2 < r ^ 2) :
    tlsOptimalWeight c r = 0 := by
  simp [tlsOptimalWeight, not_le_of_gt hout]

/-- **Exact Attainment of TLS Cost at the Optimal GNC Weight**:
$L_{\mathrm{TLS}}(r, w^\star(r; \bar{c}); \bar{c}) = \min(r^2, \bar{c}^2)$. -/
theorem tls_surrogate_at_optimal_weight (c r : ℝ) :
    tlsSurrogateTerm c r (tlsOptimalWeight c r) = tlsTruncatedTerm c r := by
  unfold tlsSurrogateTerm tlsTruncatedTerm tlsOptimalWeight
  split_ifs with h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right (le_of_not_ge h)]; ring

/-- **Black–Rangarajan / GNC Truncated Least Squares Duality (`tls_dual_weight_identity`)**:
For any finite correspondence set $s$, the primal TLS objective lower-bounds the GNC dual
surrogate over all weight vectors $w : \iota \to [0, 1]$ and is achieved with equality at
$w_i^\star = \mathrm{tlsOptimalWeight}(\bar{c}, r_i)$:
$$\sum_{i \in s} \min(r_i^2, \bar{c}^2)
  = \min_{w_i \in [0, 1]} \sum_{i \in s} \left(w_i r_i^2 + \bar{c}^2 (1 - w_i)\right).$$ -/
theorem tls_dual_weight_identity (s : Finset ι) (c : ℝ) (r w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    tlsPrimalObjective s c r ≤ tlsDualObjective s c r w ∧
      tlsDualObjective s c r (fun i => tlsOptimalWeight c (r i)) = tlsPrimalObjective s c r := by
  unfold tlsPrimalObjective tlsDualObjective
  refine ⟨?_, ?_⟩
  · apply sum_le_sum
    intro i hi
    exact tls_truncated_le_surrogate c (r i) (hw i hi).1 (hw i hi).2
  · apply sum_congr rfl
    intro i _
    exact tls_surrogate_at_optimal_weight c (r i)

/-- **TLS Robustness & Unweighted Least-Squares Dominance (`tls_objective_le_unweighted`)**:
The TLS objective is simultaneously bounded above by the ordinary unweighted least-squares cost
$\sum_{i \in s} r_i^2$ and by the outlier-clamped ceiling $|s| \bar{c}^2$, regardless of how
large individual outlier residuals grow. -/
theorem tls_objective_le_unweighted (s : Finset ι) (c : ℝ) (r : ι → ℝ) :
    0 ≤ tlsPrimalObjective s c r ∧
      tlsPrimalObjective s c r ≤ ∑ i ∈ s, (r i) ^ 2 ∧
      tlsPrimalObjective s c r ≤ (s.card : ℝ) * c ^ 2 := by
  unfold tlsPrimalObjective tlsTruncatedTerm
  refine ⟨?_, ?_, ?_⟩
  · apply sum_nonneg
    intro i _
    exact le_min (sq_nonneg (r i)) (sq_nonneg c)
  · apply sum_le_sum
    intro i _
    exact min_le_left _ _
  · calc (∑ i ∈ s, min (r i ^ 2) (c ^ 2))
        ≤ ∑ _i ∈ s, c ^ 2 := sum_le_sum (fun _ _ => min_le_right _ _)
      _ = (s.card : ℝ) * c ^ 2 := by rw [sum_const, nsmul_eq_mul]

/-! ## 3. Effective-Rank Persistent Excitation Gate for Online Calibration (`paramsd`) -/

/-- Symmetric $2 \times 2$ regressor Gram matrix
$G(a, b, d) = \begin{bmatrix} a & b \\ b & d \end{bmatrix}$. -/
def gram2Matrix (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, b; b, d]

/-- Trace $\operatorname{tr}(G) = a + d$ of the $2 \times 2$ Gram matrix. -/
def gram2Trace (a d : ℝ) : ℝ :=
  a + d

/-- Determinant $\det(G) = a d - b^2$ of the $2 \times 2$ Gram matrix. -/
def gram2Det (a b d : ℝ) : ℝ :=
  a * d - b ^ 2

/-- Squared Frobenius norm $\operatorname{tr}(G^2) = \|G\|_F^2 = a^2 + 2 b^2 + d^2$ of the
symmetric $2 \times 2$ Gram matrix. -/
def gram2FrobSq (a b d : ℝ) : ℝ :=
  a ^ 2 + 2 * b ^ 2 + d ^ 2

/-- Trace of `gram2Matrix a b d` equals `gram2Trace a d`. -/
theorem trace_gram2Matrix (a b d : ℝ) :
    (gram2Matrix a b d).trace = gram2Trace a d := by
  simp [gram2Matrix, gram2Trace, Matrix.trace, Fin.sum_univ_two]

/-- Determinant of `gram2Matrix a b d` equals `gram2Det a b d`. -/
theorem det_gram2Matrix (a b d : ℝ) :
    (gram2Matrix a b d).det = gram2Det a b d := by
  simp [gram2Matrix, gram2Det, Matrix.det_fin_two]
  ring

/-- Trace of $(G(a, b, d))^2$ equals `gram2FrobSq a b d`. -/
theorem trace_sq_gram2Matrix (a b d : ℝ) :
    (gram2Matrix a b d * gram2Matrix a b d).trace = gram2FrobSq a b d := by
  simp [gram2Matrix, gram2FrobSq, Matrix.trace, Fin.sum_univ_two]
  ring

/-- **Fundamental $2 \times 2$ Trace–Determinant Identity**
(`gram2_trace_sq_sub_trace_sq_eq_two_det`):
$$(\operatorname{tr} G)^2 - \operatorname{tr}(G^2)
  = (a + d)^2 - (a^2 + 2 b^2 + d^2) = 2 (a d - b^2) = 2 \det(G).$$ -/
theorem gram2_trace_sq_sub_trace_sq_eq_two_det (a b d : ℝ) :
    gram2Trace a d ^ 2 - gram2FrobSq a b d = 2 * gram2Det a b d := by
  unfold gram2Trace gram2FrobSq gram2Det
  ring

/-- **Symmetric Anisotropy Identity**:
$$2 \operatorname{tr}(G^2) - (\operatorname{tr} G)^2 = (a - d)^2 + 4 b^2.$$ -/
theorem gram2_two_frobSq_sub_trace_sq_eq_sum_sq (a b d : ℝ) :
    2 * gram2FrobSq a b d - gram2Trace a d ^ 2 = (a - d) ^ 2 + 4 * b ^ 2 := by
  unfold gram2FrobSq gram2Trace
  ring

/-- **Effective-Rank Trace-Square Sandwich (`gram2_trace_sq_bounds`)**:
For any $2 \times 2$ positive semidefinite Gram matrix with $\det(G) = a d - b^2 \ge 0$,
$$\operatorname{tr}(G^2) \le (\operatorname{tr} G)^2 \le 2 \operatorname{tr}(G^2).$$ -/
theorem gram2_trace_sq_bounds {a b d : ℝ} (hdet : 0 ≤ gram2Det a b d) :
    gram2FrobSq a b d ≤ gram2Trace a d ^ 2 ∧
      gram2Trace a d ^ 2 ≤ 2 * gram2FrobSq a b d := by
  have h1 := gram2_trace_sq_sub_trace_sq_eq_two_det a b d
  have h2 := gram2_two_frobSq_sub_trace_sq_eq_sum_sq a b d
  have hsq : 0 ≤ (a - d) ^ 2 + 4 * b ^ 2 := by positivity
  constructor <;> linarith

/-- **Effective-Rank Persistent Excitation Gate (`gram2_det_pos_of_effRank_gt_one`)**:
The strict effective-rank condition $(\operatorname{tr} G)^2 > \operatorname{tr}(G^2)$
(equivalently $r_{\mathrm{eff}}(G) = (\operatorname{tr} G)^2 / \operatorname{tr}(G^2) > 1$ when
$\operatorname{tr}(G^2) > 0$) holds if and only if $\det(G) > 0$, certifying full-rank persistent
excitation of the $2 \times 2$ regressor without computing square roots or eigenvalues. -/
theorem gram2_det_pos_of_effRank_gt_one (a b d : ℝ) :
    (gram2FrobSq a b d < gram2Trace a d ^ 2 ↔ 0 < gram2Det a b d) ∧
      (0 < gram2FrobSq a b d →
        1 < gram2Trace a d ^ 2 / gram2FrobSq a b d → 0 < gram2Det a b d) := by
  have hident := gram2_trace_sq_sub_trace_sq_eq_two_det a b d
  refine ⟨?_, ?_⟩
  · constructor <;> intro h <;> linarith
  · intro hfrob hdiv
    have hlt : gram2FrobSq a b d < gram2Trace a d ^ 2 :=
      ( one_lt_div hfrob ).mp hdiv
    linarith

/-- **Schur Complement Completion of Squares for $2 \times 2$ Quadratic Form**:
$$a (a x^2 + 2 b x y + d y^2) = (a x + b y)^2 + (a d - b^2) y^2.$$ -/
theorem gram2_schur_completion_of_squares (a b d x y : ℝ) :
    a * (a * x ^ 2 + 2 * b * x * y + d * y ^ 2) =
      (a * x + b * y) ^ 2 + gram2Det a b d * y ^ 2 := by
  unfold gram2Det
  ring

/-- **Strict Positive Definiteness from Effective-Rank Gate**
(`gram2_posDef_of_trace_pos_effRank_gt_one`):
If $a > 0$ (or $\operatorname{tr}(G) > 0$ with $d \ge 0$) and the effective-rank gate
$(\operatorname{tr} G)^2 > \operatorname{tr}(G^2)$ holds, then the quadratic form
$q(x, y) = a x^2 + 2 b x y + d y^2$ is strictly positive for every nonzero regressor direction
$(x, y) \ne (0, 0)$. -/
theorem gram2_posDef_of_trace_pos_effRank_gt_one {a b d x y : ℝ}
    (ha : 0 < a) (heff : gram2FrobSq a b d < gram2Trace a d ^ 2)
    (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < a * x ^ 2 + 2 * b * x * y + d * y ^ 2 := by
  have hdet : 0 < gram2Det a b d :=
    (gram2_det_pos_of_effRank_gt_one a b d).1.mp heff
  have hcomp := gram2_schur_completion_of_squares a b d x y
  have hpos_scaled : 0 < a * (a * x ^ 2 + 2 * b * x * y + d * y ^ 2) := by
    rw [hcomp]
    rcases eq_or_ne y 0 with rfl | hy
    · rcases hne with hx | hy
      · have hax : 0 < (a * x) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx)
        linarith
      · exact False.elim (hy rfl)
    · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hterm2 : 0 < gram2Det a b d * y ^ 2 := mul_pos hdet hy2
      have hterm1 : 0 ≤ (a * x + b * y) ^ 2 := sq_nonneg _
      linarith
  exact pos_of_mul_pos_right hpos_scaled ha.le

end ControlsLean.Vision
