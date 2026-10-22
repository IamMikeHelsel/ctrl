/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Kinematics of the planar two-link (RR) manipulator

Joint angles $q_1, q_2$, link lengths $l_1, l_2$. Forward kinematics
$$f(q_1, q_2) = (l_1 \cos q_1 + l_2 \cos(q_1 + q_2),\ l_1 \sin q_1 + l_2 \sin(q_1 + q_2)),$$
with Jacobian
$$J(q) = \begin{pmatrix} -l_1 \sin q_1 - l_2 \sin(q_1+q_2) & -l_2 \sin(q_1+q_2) \\
  l_1 \cos q_1 + l_2 \cos(q_1+q_2) & l_2 \cos(q_1+q_2) \end{pmatrix}.$$
Points of the plane are `ℝ × ℝ`; since the product norm on `ℝ × ℝ` is the sup norm, the
Euclidean distance from the base is written explicitly as $r(p) = \sqrt{x^2 + y^2}$.

## Main results

- `det_jacobian`: $\det J(q) = l_1 l_2 \sin q_2$.
- `det_jacobian_eq_zero_iff`: for $l_1, l_2 \neq 0$, $J(q)$ is singular iff $\sin q_2 = 0$.
- `hasFDerivAt_fk`: $J(q)$ (as the linear map `jacobianCLM`) is the Fréchet derivative of
  $f$ at $q$; `jacobianCLM_apply` identifies it with $v \mapsto J(q) v$, and
  `hasDerivAt_fk_fst_q1` … `hasDerivAt_fk_snd_q2` give the four partial derivatives.
- `radius_sq_fk`: law of cosines $x^2 + y^2 = l_1^2 + l_2^2 + 2 l_1 l_2 \cos q_2$.
- `abs_sub_le_radius_fk`, `radius_fk_le_add`: every reachable point satisfies
  $|l_1 - l_2| \le r \le l_1 + l_2$ (for $l_1, l_2 > 0$).
- `fk_ik`: inverse kinematics. If $|l_1 - l_2| \le r(p) \le l_1 + l_2$ then with the elbow
  angle $q_2 = \arccos\frac{r^2 - l_1^2 - l_2^2}{2 l_1 l_2}$ and the shoulder angle
  $q_1 = \arg(x + iy) - \arg(l_1 + l_2 e^{i q_2})$ one has $f(q_1, q_2) = p$.
- `reachable_iff`: the reachable workspace is exactly the closed annulus
  $\{p : |l_1 - l_2| \le r(p) \le l_1 + l_2\}$.
-/

namespace ControlsLean.Robotics

open Real Matrix

/-- Forward kinematics of the planar RR arm: end-effector position for joint angles
`q₁, q₂` and link lengths `l₁, l₂`. -/
noncomputable def fk (l₁ l₂ q₁ q₂ : ℝ) : ℝ × ℝ :=
  (l₁ * cos q₁ + l₂ * cos (q₁ + q₂), l₁ * sin q₁ + l₂ * sin (q₁ + q₂))

/-- The manipulator Jacobian $\partial f / \partial (q_1, q_2)$ of the planar RR arm. -/
noncomputable def jacobian (l₁ l₂ q₁ q₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(l₁ * sin q₁) - l₂ * sin (q₁ + q₂), -(l₂ * sin (q₁ + q₂));
     l₁ * cos q₁ + l₂ * cos (q₁ + q₂), l₂ * cos (q₁ + q₂)]

/-- Euclidean distance of a planar point from the origin, $\sqrt{x^2 + y^2}$. -/
noncomputable def radius (p : ℝ × ℝ) : ℝ := √(p.1 ^ 2 + p.2 ^ 2)

/-- **Jacobian determinant** of the planar RR arm: $\det J(q) = l_1 l_2 \sin q_2$. -/
theorem det_jacobian (l₁ l₂ q₁ q₂ : ℝ) :
    (jacobian l₁ l₂ q₁ q₂).det = l₁ * l₂ * sin q₂ := by
  have h : sin q₂ = sin (q₁ + q₂) * cos q₁ - cos (q₁ + q₂) * sin q₁ := by
    rw [← sin_sub]; ring_nf
  rw [jacobian, Matrix.det_fin_two_of, h]
  ring

/-- **Kinematic singularities**: for nonzero link lengths the Jacobian is singular exactly
when $\sin q_2 = 0$, i.e. the arm is fully stretched or folded ($q_2 \equiv 0 \bmod \pi$). -/
theorem det_jacobian_eq_zero_iff {l₁ l₂ : ℝ} (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0) (q₁ q₂ : ℝ) :
    (jacobian l₁ l₂ q₁ q₂).det = 0 ↔ sin q₂ = 0 := by
  rw [det_jacobian]
  simp [h₁, h₂]

/-- Singularity in the form $q_2 = k\pi$ for some integer $k$. -/
theorem det_jacobian_eq_zero_iff_exists_int {l₁ l₂ : ℝ} (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0)
    (q₁ q₂ : ℝ) : (jacobian l₁ l₂ q₁ q₂).det = 0 ↔ ∃ k : ℤ, (k : ℝ) * π = q₂ := by
  rw [det_jacobian_eq_zero_iff h₁ h₂, sin_eq_zero_iff]

/-- The Jacobian as a continuous linear map `ℝ × ℝ →L[ℝ] ℝ × ℝ`. -/
noncomputable def jacobianCLM (l₁ l₂ q₁ q₂ : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((-(l₁ * sin q₁) - l₂ * sin (q₁ + q₂)) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (-(l₂ * sin (q₁ + q₂))) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((l₁ * cos q₁ + l₂ * cos (q₁ + q₂)) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (l₂ * cos (q₁ + q₂)) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- `jacobianCLM` acts on a joint velocity $v$ as the matrix product $J(q) v$. -/
theorem jacobianCLM_apply (l₁ l₂ q₁ q₂ : ℝ) (v : ℝ × ℝ) :
    jacobianCLM l₁ l₂ q₁ q₂ v =
      ((jacobian l₁ l₂ q₁ q₂ *ᵥ ![v.1, v.2]) 0, (jacobian l₁ l₂ q₁ q₂ *ᵥ ![v.1, v.2]) 1) := by
  simp [jacobianCLM, jacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The Jacobian is the derivative of forward kinematics**:
$f$ has Fréchet derivative $J(q)$ at every $q = (q_1, q_2)$. -/
theorem hasFDerivAt_fk (l₁ l₂ : ℝ) (q : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => fk l₁ l₂ q.1 q.2) (jacobianCLM l₁ l₂ q.1 q.2) q := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have h12 : HasFDerivAt (fun q : ℝ × ℝ => q.1 + q.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  have hx := ((h1.cos).const_mul l₁).add ((h12.cos).const_mul l₂)
  have hy := ((h1.sin).const_mul l₁).add ((h12.sin).const_mul l₂)
  convert hx.prodMk hy using 1
  · ext v <;> simp [fk]
  · ext <;> simp [jacobianCLM]
    ring

/-- Partial derivative $\partial f_x / \partial q_1 = J_{00}$. -/
theorem hasDerivAt_fk_fst_q1 (l₁ l₂ q₁ q₂ : ℝ) :
    HasDerivAt (fun t => (fk l₁ l₂ t q₂).1) (jacobian l₁ l₂ q₁ q₂ 0 0) q₁ := by
  have h := ((hasDerivAt_id q₁).cos.const_mul l₁).add
    (((hasDerivAt_id q₁).add_const q₂).cos.const_mul l₂)
  convert h using 1
  · funext t; simp [fk]
  · simp [jacobian]; ring

/-- Partial derivative $\partial f_x / \partial q_2 = J_{01}$. -/
theorem hasDerivAt_fk_fst_q2 (l₁ l₂ q₁ q₂ : ℝ) :
    HasDerivAt (fun t => (fk l₁ l₂ q₁ t).1) (jacobian l₁ l₂ q₁ q₂ 0 1) q₂ := by
  have h := (((hasDerivAt_id q₂).const_add q₁).cos.const_mul l₂).const_add (l₁ * cos q₁)
  convert h using 1 <;> simp [fk, jacobian]

/-- Partial derivative $\partial f_y / \partial q_1 = J_{10}$. -/
theorem hasDerivAt_fk_snd_q1 (l₁ l₂ q₁ q₂ : ℝ) :
    HasDerivAt (fun t => (fk l₁ l₂ t q₂).2) (jacobian l₁ l₂ q₁ q₂ 1 0) q₁ := by
  have h := ((hasDerivAt_id q₁).sin.const_mul l₁).add
    (((hasDerivAt_id q₁).add_const q₂).sin.const_mul l₂)
  convert h using 1
  · funext t; simp [fk]
  · simp [jacobian]

/-- Partial derivative $\partial f_y / \partial q_2 = J_{11}$. -/
theorem hasDerivAt_fk_snd_q2 (l₁ l₂ q₁ q₂ : ℝ) :
    HasDerivAt (fun t => (fk l₁ l₂ q₁ t).2) (jacobian l₁ l₂ q₁ q₂ 1 1) q₂ := by
  have h := (((hasDerivAt_id q₂).const_add q₁).sin.const_mul l₂).const_add (l₁ * sin q₁)
  convert h using 1 <;> simp [fk, jacobian]

/-- **Law of cosines** for the RR arm:
$x^2 + y^2 = l_1^2 + l_2^2 + 2 l_1 l_2 \cos q_2$. -/
theorem radius_sq_fk (l₁ l₂ q₁ q₂ : ℝ) :
    (fk l₁ l₂ q₁ q₂).1 ^ 2 + (fk l₁ l₂ q₁ q₂).2 ^ 2
      = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos q₂ := by
  have h : cos q₂ = cos (q₁ + q₂) * cos q₁ + sin (q₁ + q₂) * sin q₁ := by
    rw [← cos_sub]; ring_nf
  have h1 := sin_sq_add_cos_sq q₁
  have h2 := sin_sq_add_cos_sq (q₁ + q₂)
  simp only [fk]
  rw [h]
  linear_combination l₁ ^ 2 * h1 + l₂ ^ 2 * h2

/-- Squared reach in terms of `radius`. -/
theorem radius_fk_sq (l₁ l₂ q₁ q₂ : ℝ) :
    radius (fk l₁ l₂ q₁ q₂) ^ 2 = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos q₂ := by
  rw [radius, sq_sqrt (by positivity), radius_sq_fk]

/-- **Outer workspace boundary**: the end effector is never farther than $l_1 + l_2$. -/
theorem radius_fk_le_add {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) (q₁ q₂ : ℝ) :
    radius (fk l₁ l₂ q₁ q₂) ≤ l₁ + l₂ := by
  have hr := radius_fk_sq l₁ l₂ q₁ q₂
  have hc := cos_le_one q₂
  have h0 : 0 ≤ radius (fk l₁ l₂ q₁ q₂) := sqrt_nonneg _
  have : radius (fk l₁ l₂ q₁ q₂) ^ 2 ≤ (l₁ + l₂) ^ 2 := by
    rw [hr]; nlinarith [mul_pos h₁ h₂]
  exact (sq_le_sq₀ h0 (by positivity)).1 this

/-- **Inner workspace boundary**: the end effector is never closer than $|l_1 - l_2|$. -/
theorem abs_sub_le_radius_fk {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) (q₁ q₂ : ℝ) :
    |l₁ - l₂| ≤ radius (fk l₁ l₂ q₁ q₂) := by
  have hr := radius_fk_sq l₁ l₂ q₁ q₂
  have hc := neg_one_le_cos q₂
  have h0 : 0 ≤ radius (fk l₁ l₂ q₁ q₂) := sqrt_nonneg _
  have : (l₁ - l₂) ^ 2 ≤ radius (fk l₁ l₂ q₁ q₂) ^ 2 := by
    rw [hr]; nlinarith [mul_pos h₁ h₂]
  rw [← sq_abs (l₁ - l₂)] at this
  exact (sq_le_sq₀ (abs_nonneg _) h0).1 this

/-! ### Inverse kinematics -/

/-- Elbow angle of the inverse-kinematics solution:
$q_2 = \arccos\frac{r^2 - l_1^2 - l_2^2}{2 l_1 l_2}$ (the "elbow-down" branch). -/
noncomputable def ikElbow (l₁ l₂ : ℝ) (p : ℝ × ℝ) : ℝ :=
  arccos ((radius p ^ 2 - l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * l₂))

/-- Shoulder angle of the inverse-kinematics solution:
$q_1 = \arg(x + iy) - \arg(l_1 + l_2 e^{i q_2})$. -/
noncomputable def ikShoulder (l₁ l₂ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Complex.arg (p.1 + p.2 * Complex.I)
    - Complex.arg (l₁ + l₂ * Complex.exp (ikElbow l₁ l₂ p * Complex.I))

/-- Complex form of forward kinematics:
$x + iy = (l_1 + l_2 e^{i q_2}) e^{i q_1}$. -/
theorem fk_complex (l₁ l₂ q₁ q₂ : ℝ) :
    ((fk l₁ l₂ q₁ q₂).1 : ℂ) + (fk l₁ l₂ q₁ q₂).2 * Complex.I
      = (l₁ + l₂ * Complex.exp (q₂ * Complex.I)) * Complex.exp (q₁ * Complex.I) := by
  apply Complex.ext <;>
    simp [fk, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, cos_add, sin_add,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    ring

private theorem norm_ofProd (p : ℝ × ℝ) : ‖(p.1 : ℂ) + p.2 * Complex.I‖ = radius p := by
  rw [Complex.norm_def, radius, Complex.normSq_apply]
  simp [sq]

/-- **Inverse kinematics correctness**: every point of the annulus
$|l_1 - l_2| \le r(p) \le l_1 + l_2$ is reached by the joint angles
$(q_1, q_2) =$ (`ikShoulder`, `ikElbow`). -/
theorem fk_ik {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) {p : ℝ × ℝ}
    (hlo : |l₁ - l₂| ≤ radius p) (hhi : radius p ≤ l₁ + l₂) :
    fk l₁ l₂ (ikShoulder l₁ l₂ p) (ikElbow l₁ l₂ p) = p := by
  set r := radius p with hr
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have h12 : 0 < 2 * l₁ * l₂ := by positivity
  have hlo2 : (l₁ - l₂) ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hlo 2
  have hhi2 : r ^ 2 ≤ (l₁ + l₂) ^ 2 := pow_le_pow_left₀ hr0 hhi 2
  have hc1 : -1 ≤ (r ^ 2 - l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * l₂) := by
    rw [le_div_iff₀ h12]; nlinarith
  have hc2 : (r ^ 2 - l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * l₂) ≤ 1 := by
    rw [div_le_iff₀ h12]; nlinarith
  have hcos : cos (ikElbow l₁ l₂ p) = (r ^ 2 - l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * l₂) :=
    cos_arccos hc1 hc2
  set q₂ := ikElbow l₁ l₂ p
  set w : ℂ := l₁ + l₂ * Complex.exp (q₂ * Complex.I) with hw
  set z : ℂ := (p.1 : ℂ) + p.2 * Complex.I with hz
  have hwn : ‖w‖ = r := by
    have hsq : ‖w‖ ^ 2 = r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [hw, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im]
      have hs := sin_sq_add_cos_sq q₂
      have : r ^ 2 = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos q₂ := by
        rw [hcos]; field_simp; ring
      rw [this]; linear_combination l₂ ^ 2 * hs
    exact (sq_eq_sq₀ (norm_nonneg _) hr0).1 hsq
  have hzn : ‖z‖ = r := norm_ofProd p
  have key : w * Complex.exp (ikShoulder l₁ l₂ p * Complex.I) = z := by
    have e : ikShoulder l₁ l₂ p = Complex.arg z - Complex.arg w := rfl
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [hwn, hzn, mul_assoc, ← Complex.exp_add, e]
    congr 2
    push_cast; ring
  have hc := fk_complex l₁ l₂ (ikShoulder l₁ l₂ p) q₂
  rw [← hw, key, hz] at hc
  have h1 := congrArg Complex.re hc
  have h2 := congrArg Complex.im hc
  simp at h1 h2
  exact Prod.ext h1 h2

/-- **Reachable workspace of the planar RR arm**: a point $p$ is reachable,
i.e. $p = f(q_1, q_2)$ for some joint angles, iff $|l_1 - l_2| \le r(p) \le l_1 + l_2$. -/
theorem reachable_iff {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) (p : ℝ × ℝ) :
    (∃ q₁ q₂ : ℝ, fk l₁ l₂ q₁ q₂ = p) ↔ |l₁ - l₂| ≤ radius p ∧ radius p ≤ l₁ + l₂ := by
  constructor
  · rintro ⟨q₁, q₂, rfl⟩
    exact ⟨abs_sub_le_radius_fk h₁ h₂ q₁ q₂, radius_fk_le_add h₁ h₂ q₁ q₂⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨_, _, fk_ik h₁ h₂ hlo hhi⟩

end ControlsLean.Robotics
