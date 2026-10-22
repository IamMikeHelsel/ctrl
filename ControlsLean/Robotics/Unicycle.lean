/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Unicycle / Differential-Drive Kinematics and Kanayama Tracking

The unicycle model of a wheeled mobile robot with pose $(x, y, \theta)$ is
$$\dot x = v \cos\theta, \qquad \dot y = v \sin\theta, \qquad \dot\theta = \omega.$$

## Main results

1. **Differential drive.** Wheel speeds $(\omega_L, \omega_R)$, wheel radius $r$ and track
   width $w$ give $(v, \omega) = (r(\omega_R + \omega_L)/2,\ r(\omega_R - \omega_L)/w)$.
   - `diffDriveInverse_diffDrive`, `diffDrive_diffDriveInverse`: for $r, w \ne 0$ the explicit
     map `diffDriveInverse` is a two-sided inverse; `diffDriveEquiv` packages it as an `Equiv`
     and `diffDrive_bijective` states bijectivity.
2. **Exact arc odometry.** For constant $(v, \omega)$ with $\omega \ne 0$,
   $x(t) = x_0 + \tfrac{v}{\omega}(\sin(\theta_0 + \omega t) - \sin\theta_0)$,
   $y(t) = y_0 - \tfrac{v}{\omega}(\cos(\theta_0 + \omega t) - \cos\theta_0)$,
   $\theta(t) = \theta_0 + \omega t$.
   - `hasDerivAt_arcX`, `hasDerivAt_arcY`, `hasDerivAt_arcTheta`: these solve the unicycle
     ODE; `arcX_zero`, `arcY_zero`, `arcTheta_zero`: initial condition at $t = 0$.
   - `tendsto_arcX_straight`, `tendsto_arcY_straight`: as $\omega \to 0$ ($\omega \ne 0$)
     the update tends to the straight-line motion
     $(x_0 + vT\cos\theta_0,\ y_0 + vT\sin\theta_0)$.
3. **Nonholonomic constraint.**
   - `nonholonomic_constraint`: any differentiable unicycle trajectory satisfies
     $\dot x \sin\theta - \dot y \cos\theta = 0$ (no sideways slip);
     `arc_nonholonomic` specialises it to the exact arc.
4. **Kanayama tracking.** Error in the robot frame
   $e = \operatorname{Rot}(-\theta)(p_r - p)$, $e_\theta = \theta_r - \theta$.
   - `hasDerivAt_errX`, `hasDerivAt_errY`, `hasDerivAt_errTheta`: the error dynamics
     $\dot e_x = \omega e_y - v + v_r\cos e_\theta$,
     $\dot e_y = -\omega e_x + v_r \sin e_\theta$, $\dot e_\theta = \omega_r - \omega$.
   - `kanayamaV_nonneg`: $V = \tfrac12(e_x^2 + e_y^2) + (1 - \cos e_\theta)/k_y \ge 0$
     for $k_y > 0$.
   - `hasDerivAt_kanayamaV`: under $v = v_r\cos e_\theta + k_x e_x$,
     $\omega = \omega_r + v_r k_y e_y + k_\theta \sin e_\theta$ (and $k_y \ne 0$),
     $\dot V = -k_x e_x^2 - (k_\theta / k_y)\sin^2 e_\theta$;
     `kanayamaV_deriv_nonpos`: this is $\le 0$ when $k_x, k_\theta \ge 0$, $k_y > 0$.
   - `hasDerivAt_kanayamaV_classic`, `kanayamaV_classic_deriv_nonpos`: for Kanayama's
     original law $\omega = \omega_r + v_r(k_y e_y + k_\theta \sin e_\theta)$,
     $\dot V = -k_x e_x^2 - v_r (k_\theta / k_y)\sin^2 e_\theta$, which is $\le 0$ when
     additionally $v_r \ge 0$.
-/

namespace ControlsLean.Robotics

open Real Filter Topology

/-! ## 1. Differential drive -/

/-- Differential-drive forward kinematics: wheel speeds `(ωL, ωR)` ↦ body twist `(v, ω)`. -/
noncomputable def diffDrive (r w : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (r * (q.2 + q.1) / 2, r * (q.2 - q.1) / w)

/-- Differential-drive inverse kinematics: body twist `(v, ω)` ↦ wheel speeds `(ωL, ωR)`. -/
noncomputable def diffDriveInverse (r w : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  ((u.1 - w * u.2 / 2) / r, (u.1 + w * u.2 / 2) / r)

theorem diffDriveInverse_diffDrive {r w : ℝ} (hr : r ≠ 0) (hw : w ≠ 0) (q : ℝ × ℝ) :
    diffDriveInverse r w (diffDrive r w q) = q := by
  obtain ⟨a, b⟩ := q
  simp only [diffDriveInverse, diffDrive, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

theorem diffDrive_diffDriveInverse {r w : ℝ} (hr : r ≠ 0) (hw : w ≠ 0) (u : ℝ × ℝ) :
    diffDrive r w (diffDriveInverse r w u) = u := by
  obtain ⟨a, b⟩ := u
  simp only [diffDriveInverse, diffDrive, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- For nonzero wheel radius and track width, differential-drive kinematics is a bijection
between wheel speeds and body twists. -/
noncomputable def diffDriveEquiv {r w : ℝ} (hr : r ≠ 0) (hw : w ≠ 0) : ℝ × ℝ ≃ ℝ × ℝ where
  toFun := diffDrive r w
  invFun := diffDriveInverse r w
  left_inv := diffDriveInverse_diffDrive hr hw
  right_inv := diffDrive_diffDriveInverse hr hw

theorem diffDrive_bijective {r w : ℝ} (hr : r ≠ 0) (hw : w ≠ 0) :
    Function.Bijective (diffDrive r w) :=
  (diffDriveEquiv hr hw).bijective

/-! ## 2. Exact arc odometry -/

/-- `x`-coordinate of the exact constant-twist (circular arc) pose update. -/
noncomputable def arcX (x θ v ω t : ℝ) : ℝ := x + v / ω * (sin (θ + ω * t) - sin θ)

/-- `y`-coordinate of the exact constant-twist (circular arc) pose update. -/
noncomputable def arcY (y θ v ω t : ℝ) : ℝ := y - v / ω * (cos (θ + ω * t) - cos θ)

/-- Heading of the exact constant-twist pose update. -/
def arcTheta (θ ω t : ℝ) : ℝ := θ + ω * t

theorem arcX_zero (x θ v ω : ℝ) : arcX x θ v ω 0 = x := by simp [arcX]

theorem arcY_zero (y θ v ω : ℝ) : arcY y θ v ω 0 = y := by simp [arcY]

theorem arcTheta_zero (θ ω : ℝ) : arcTheta θ ω 0 = θ := by simp [arcTheta]

theorem hasDerivAt_arcTheta (θ ω t : ℝ) : HasDerivAt (arcTheta θ ω) ω t := by
  have h : HasDerivAt (fun s => θ + ω * s) (ω * 1) t := ((hasDerivAt_id t).const_mul ω).const_add θ
  exact h.congr_deriv (mul_one ω)

theorem hasDerivAt_arcX (x θ v : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (arcX x θ v ω) (v * cos (arcTheta θ ω t)) t := by
  have h := (((hasDerivAt_arcTheta θ ω t).sin.sub_const (sin θ)).const_mul (v / ω)).const_add x
  exact h.congr_deriv (by field_simp)

theorem hasDerivAt_arcY (y θ v : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (arcY y θ v ω) (v * sin (arcTheta θ ω t)) t := by
  have h := (((hasDerivAt_arcTheta θ ω t).cos.sub_const (cos θ)).const_mul (v / ω)).const_sub y
  exact h.congr_deriv (by field_simp)

/-- `(sin (θ + ωT) - sin θ) / ω → T cos θ` as `ω → 0`. -/
private theorem tendsto_sin_slope (θ T : ℝ) :
    Tendsto (fun ω : ℝ => ω⁻¹ * (sin (θ + ω * T) - sin θ)) (𝓝[≠] 0) (𝓝 (T * cos θ)) := by
  have h : HasDerivAt (fun ω : ℝ => sin (θ + ω * T)) (cos (θ + 0 * T) * T) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const T).const_add θ).sin.congr_deriv (by simp)
  have := hasDerivAt_iff_tendsto_slope_zero.mp h
  simpa [mul_comm] using this

/-- `(cos (θ + ωT) - cos θ) / ω → -T sin θ` as `ω → 0`. -/
private theorem tendsto_cos_slope (θ T : ℝ) :
    Tendsto (fun ω : ℝ => ω⁻¹ * (cos (θ + ω * T) - cos θ)) (𝓝[≠] 0) (𝓝 (-(T * sin θ))) := by
  have h : HasDerivAt (fun ω : ℝ => cos (θ + ω * T)) (-sin (θ + 0 * T) * T) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const T).const_add θ).cos.congr_deriv (by simp)
  have := hasDerivAt_iff_tendsto_slope_zero.mp h
  simpa [mul_comm] using this

/-- As `ω → 0`, the exact arc `x`-update tends to straight-line motion `x + v T cos θ`. -/
theorem tendsto_arcX_straight (x θ v T : ℝ) :
    Tendsto (fun ω => arcX x θ v ω T) (𝓝[≠] 0) (𝓝 (x + v * T * cos θ)) := by
  have := ((tendsto_sin_slope θ T).const_mul v).const_add x
  refine this.congr' (Eventually.of_forall fun ω => ?_) |>.trans ?_
  · simp [arcX, div_eq_mul_inv, mul_assoc]
  · simp [mul_assoc]

/-- As `ω → 0`, the exact arc `y`-update tends to straight-line motion `y + v T sin θ`. -/
theorem tendsto_arcY_straight (y θ v T : ℝ) :
    Tendsto (fun ω => arcY y θ v ω T) (𝓝[≠] 0) (𝓝 (y + v * T * sin θ)) := by
  have := ((tendsto_cos_slope θ T).const_mul v).const_sub y
  refine this.congr' (Eventually.of_forall fun ω => ?_) |>.trans ?_
  · simp [arcY, div_eq_mul_inv, mul_assoc]
  · simp [mul_assoc, sub_eq_add_neg]

/-! ## 3. Nonholonomic constraint -/

/-- A unicycle trajectory never slips sideways: `ẋ sin θ - ẏ cos θ = 0`. -/
theorem nonholonomic_constraint {px py θ : ℝ → ℝ} {v : ℝ} {t : ℝ}
    (hx : HasDerivAt px (v * cos (θ t)) t) (hy : HasDerivAt py (v * sin (θ t)) t) :
    deriv px t * sin (θ t) - deriv py t * cos (θ t) = 0 := by
  rw [hx.deriv, hy.deriv]; ring

/-- The exact arc odometry satisfies the nonholonomic constraint. -/
theorem arc_nonholonomic (x y θ v : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    deriv (arcX x θ v ω) t * sin (arcTheta θ ω t)
      - deriv (arcY y θ v ω) t * cos (arcTheta θ ω t) = 0 :=
  nonholonomic_constraint (hasDerivAt_arcX x θ v hω t) (hasDerivAt_arcY y θ v hω t)

/-! ## 4. Kanayama tracking error -/

/-- Longitudinal tracking error: first component of `Rot(-θ) (p_r - p)`. -/
noncomputable def errX (x y θ xr yr : ℝ) : ℝ := cos θ * (xr - x) + sin θ * (yr - y)

/-- Lateral tracking error: second component of `Rot(-θ) (p_r - p)`. -/
noncomputable def errY (x y θ xr yr : ℝ) : ℝ := -sin θ * (xr - x) + cos θ * (yr - y)

/-- Kanayama's Lyapunov function `½ (e_x² + e_y²) + (1 - cos e_θ) / k_y`. -/
noncomputable def kanayamaV (ky ex ey eθ : ℝ) : ℝ := (ex ^ 2 + ey ^ 2) / 2 + (1 - cos eθ) / ky

section ErrorDynamics

variable {x y θ xr yr θr : ℝ → ℝ} {v ω vr ωr t : ℝ}

theorem hasDerivAt_errX
    (hx : HasDerivAt x (v * cos (θ t)) t) (hy : HasDerivAt y (v * sin (θ t)) t)
    (hθ : HasDerivAt θ ω t)
    (hxr : HasDerivAt xr (vr * cos (θr t)) t) (hyr : HasDerivAt yr (vr * sin (θr t)) t) :
    HasDerivAt (fun s => errX (x s) (y s) (θ s) (xr s) (yr s))
      (ω * errY (x t) (y t) (θ t) (xr t) (yr t) - v + vr * cos (θr t - θ t)) t := by
  have h := (hθ.cos.fun_mul (hxr.fun_sub hx)).fun_add (hθ.sin.fun_mul (hyr.fun_sub hy))
  refine h.congr_deriv ?_
  simp only [errY, cos_sub]
  linear_combination (-v) * sin_sq_add_cos_sq (θ t)

theorem hasDerivAt_errY
    (hx : HasDerivAt x (v * cos (θ t)) t) (hy : HasDerivAt y (v * sin (θ t)) t)
    (hθ : HasDerivAt θ ω t)
    (hxr : HasDerivAt xr (vr * cos (θr t)) t) (hyr : HasDerivAt yr (vr * sin (θr t)) t) :
    HasDerivAt (fun s => errY (x s) (y s) (θ s) (xr s) (yr s))
      (-ω * errX (x t) (y t) (θ t) (xr t) (yr t) + vr * sin (θr t - θ t)) t := by
  have h := (hθ.sin.fun_neg.fun_mul (hxr.fun_sub hx)).fun_add (hθ.cos.fun_mul (hyr.fun_sub hy))
  refine h.congr_deriv ?_
  simp only [errX, sin_sub]
  ring

theorem hasDerivAt_errTheta (hθ : HasDerivAt θ ω t) (hθr : HasDerivAt θr ωr t) :
    HasDerivAt (fun s => θr s - θ s) (ωr - ω) t :=
  hθr.fun_sub hθ

end ErrorDynamics

theorem kanayamaV_nonneg {ky : ℝ} (hky : 0 < ky) (ex ey eθ : ℝ) :
    0 ≤ kanayamaV ky ex ey eθ := by
  unfold kanayamaV
  have h : 0 ≤ (1 - cos eθ) / ky := div_nonneg (sub_nonneg.2 (cos_le_one eθ)) hky.le
  positivity

/-- Chain rule for `V` along arbitrary differentiable error signals. -/
theorem hasDerivAt_kanayamaV_comp {ex ey eθ : ℝ → ℝ} {dex dey deθ t : ℝ} (ky : ℝ)
    (hex : HasDerivAt ex dex t) (hey : HasDerivAt ey dey t) (heθ : HasDerivAt eθ deθ t) :
    HasDerivAt (fun s => kanayamaV ky (ex s) (ey s) (eθ s))
      (ex t * dex + ey t * dey + sin (eθ t) * deθ / ky) t := by
  have h := (((hex.fun_pow 2).fun_add (hey.fun_pow 2)).div_const 2).fun_add
    ((heθ.cos.const_sub 1).div_const ky)
  refine h.congr_deriv ?_
  push_cast
  ring

section Lyapunov

variable {x y θ xr yr θr : ℝ → ℝ} {v ω vr ωr t : ℝ} {kx ky kθ : ℝ}

/-- Along the closed loop with the Kanayama-type law
`v = v_r cos e_θ + k_x e_x`, `ω = ω_r + v_r k_y e_y + k_θ sin e_θ`, the Lyapunov function
`V = ½ (e_x² + e_y²) + (1 - cos e_θ) / k_y` has `V̇ = -k_x e_x² - (k_θ / k_y) sin² e_θ`. -/
theorem hasDerivAt_kanayamaV (hky : ky ≠ 0)
    (hx : HasDerivAt x (v * cos (θ t)) t) (hy : HasDerivAt y (v * sin (θ t)) t)
    (hθ : HasDerivAt θ ω t)
    (hxr : HasDerivAt xr (vr * cos (θr t)) t) (hyr : HasDerivAt yr (vr * sin (θr t)) t)
    (hθr : HasDerivAt θr ωr t)
    (hv : v = vr * cos (θr t - θ t) + kx * errX (x t) (y t) (θ t) (xr t) (yr t))
    (hω : ω = ωr + vr * ky * errY (x t) (y t) (θ t) (xr t) (yr t)
      + kθ * sin (θr t - θ t)) :
    HasDerivAt
      (fun s => kanayamaV ky (errX (x s) (y s) (θ s) (xr s) (yr s))
        (errY (x s) (y s) (θ s) (xr s) (yr s)) (θr s - θ s))
      (-kx * errX (x t) (y t) (θ t) (xr t) (yr t) ^ 2 - kθ / ky * sin (θr t - θ t) ^ 2) t := by
  refine (hasDerivAt_kanayamaV_comp ky (hasDerivAt_errX hx hy hθ hxr hyr)
    (hasDerivAt_errY hx hy hθ hxr hyr) (hasDerivAt_errTheta hθ hθr)).congr_deriv ?_
  rw [hω, hv]
  field_simp
  ring

/-- With `k_x, k_θ ≥ 0` and `k_y > 0`, the Kanayama Lyapunov derivative is nonpositive. -/
theorem kanayamaV_deriv_nonpos {kx ky kθ : ℝ} (hkx : 0 ≤ kx) (hky : 0 < ky) (hkθ : 0 ≤ kθ)
    (ex eθ : ℝ) : -kx * ex ^ 2 - kθ / ky * sin eθ ^ 2 ≤ 0 := by
  have h1 : 0 ≤ kx * ex ^ 2 := by positivity
  have h2 : 0 ≤ kθ / ky * sin eθ ^ 2 := by positivity
  linarith

/-- Kanayama's original law `ω = ω_r + v_r (k_y e_y + k_θ sin e_θ)` gives
`V̇ = -k_x e_x² - v_r (k_θ / k_y) sin² e_θ`. -/
theorem hasDerivAt_kanayamaV_classic (hky : ky ≠ 0)
    (hx : HasDerivAt x (v * cos (θ t)) t) (hy : HasDerivAt y (v * sin (θ t)) t)
    (hθ : HasDerivAt θ ω t)
    (hxr : HasDerivAt xr (vr * cos (θr t)) t) (hyr : HasDerivAt yr (vr * sin (θr t)) t)
    (hθr : HasDerivAt θr ωr t)
    (hv : v = vr * cos (θr t - θ t) + kx * errX (x t) (y t) (θ t) (xr t) (yr t))
    (hω : ω = ωr + vr * (ky * errY (x t) (y t) (θ t) (xr t) (yr t)
      + kθ * sin (θr t - θ t))) :
    HasDerivAt
      (fun s => kanayamaV ky (errX (x s) (y s) (θ s) (xr s) (yr s))
        (errY (x s) (y s) (θ s) (xr s) (yr s)) (θr s - θ s))
      (-kx * errX (x t) (y t) (θ t) (xr t) (yr t) ^ 2
        - vr * (kθ / ky) * sin (θr t - θ t) ^ 2) t := by
  refine (hasDerivAt_kanayamaV_comp ky (hasDerivAt_errX hx hy hθ hxr hyr)
    (hasDerivAt_errY hx hy hθ hxr hyr) (hasDerivAt_errTheta hθ hθr)).congr_deriv ?_
  rw [hω, hv]
  field_simp
  ring

/-- For the original Kanayama law, `V̇ ≤ 0` when `k_x, k_θ ≥ 0`, `k_y > 0`, `v_r ≥ 0`. -/
theorem kanayamaV_classic_deriv_nonpos {kx ky kθ vr : ℝ} (hkx : 0 ≤ kx) (hky : 0 < ky)
    (hkθ : 0 ≤ kθ) (hvr : 0 ≤ vr) (ex eθ : ℝ) :
    -kx * ex ^ 2 - vr * (kθ / ky) * sin eθ ^ 2 ≤ 0 := by
  have h1 : 0 ≤ kx * ex ^ 2 := by positivity
  have h2 : 0 ≤ vr * (kθ / ky) * sin eθ ^ 2 := by positivity
  linarith

end Lyapunov

end ControlsLean.Robotics
