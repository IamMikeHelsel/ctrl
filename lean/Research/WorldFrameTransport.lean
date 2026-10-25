import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Robotics Cards R06, R07, R03, R05: World-Frame Transport, Redundant Nullspace Allocation & Clock-Warp Semantics

Formal verification of four core robotics execution & kinematics problems from the Crossover campaign:
1. **Card R06 (World-Frame Derivative Transport on Rotating Bases)**:
   - Proves the exact 3D Euler–Centripetal Orthogonality Theorem (`euler_centripetal_orthogonal`):
     for any lever arm $p \in \mathbb{R}^3$ on a base rotating with angular velocity $\omega = \dot{\theta} \hat{k}$
     and angular acceleration $\alpha = \ddot{\theta} \hat{k}$ around a unit axis $\hat{k}$ ($\|\hat{k}\|^2 = 1$),
     the Euler acceleration $\alpha \times p$ and the centripetal acceleration $\omega \times (\omega \times p)$
     are strictly orthogonal: $(\alpha \times p) \cdot (\omega \times (\omega \times p)) = 0$.
   - Proves the exact Pythagorean acceleration magnitude identity (`euler_centripetal_sqNorm_exact`):
     $$\|\alpha \times p + \omega \times (\omega \times p)\|^2 = (\ddot{\theta}^2 + \dot{\theta}^4) \|\hat{k} \times p\|^2 = (\ddot{\theta}^2 + \dot{\theta}^4)(\|p\|^2 - (\hat{k} \cdot p)^2).$$
   - Proves that a body-frame hold ($v_B = 0, a_B = 0$) violates any world-frame acceleration
     limit $A_{\max}$ whenever $(\ddot{\theta}^2 + \dot{\theta}^4) \|\hat{k} \times p\|^2 > A_{\max}^2$ (`body_hold_violates_world_accel`).

2. **Card R07 (Minimal-Intervention Nullspace Allocation on Redundant Arms)**:
   - For a 3-DOF redundant manipulator with task Jacobian row $J \in \mathbb{R}^3$ ($\|J\|^2 > 0$),
     task velocity target $v_{\text{task}}$, and nominal posture velocity $q_{\text{nom}}$,
     proves that the Moore–Penrose minimal-intervention projector
     $$q^* = q_{\text{nom}} + \frac{v_{\text{task}} - J \cdot q_{\text{nom}}}{\|J\|^2} \bullet J$$
     simultaneously:
     - Achieves exact task velocity: $J \cdot q^* = v_{\text{task}}$ (`minimal_intervention_achieves_task`),
     - Leaves every nullspace posture direction $z \perp J$ completely undisturbed:
       $z \cdot q^* = z \cdot q_{\text{nom}}$ (`minimal_intervention_preserves_nullspace`),
     - Uniquely minimizes the $L^2$ intervention norm $\|q - q_{\text{nom}}\|^2$ across all task-feasible
       joint velocities via the exact Pythagorean identity
       $\|q - q_{\text{nom}}\|^2 = \|q^* - q_{\text{nom}}\|^2 + \|q - q^*\|^2$ (`minimal_intervention_pythagorean_optimality`).

3. **Card R03 (Clock-Warp Derivative Chain Rules & Piecewise Clock-Slew Velocity Jump)**:
   - Proves the exact 1st, 2nd, and 3rd order time-warp chain rule for a trajectory evaluated
     through a distorted clock $\tau(t)$ (`HasDerivAt`):
     $$\begin{aligned}
     \frac{d}{dt} q(\tau(t)) &= \dot{\tau}(t) q'(\tau(t)), \\
     \frac{d^2}{dt^2} q(\tau(t)) &= \ddot{\tau}(t) q'(\tau(t)) + \dot{\tau}(t)^2 q''(\tau(t)), \\
     \frac{d^3}{dt^3} q(\tau(t)) &= \dddot{\tau}(t) q'(\tau(t)) + 3 \dot{\tau}(t) \ddot{\tau}(t) q''(\tau(t)) + \dot{\tau}(t)^3 q'''(\tau(t)).
     \end{aligned}$$
   - Proves with 0 `sorry` (`clock_slew_breaks_spline_differentiability`) that evaluating the smooth
     $C^3$ four-box position spline across a continuous piecewise-linear clock rate change ($\dot{\tau}_- = 3/2$
     to $\dot{\tau}_+ = 1/2$ at $t = 0$) destroys differentiability at $t = 0$ with an exact velocity jump of $-23/480$.

4. **Card R05 (Bounded Retained-History Storage via Minimum-Spacing Arrival Curves)**:
   - Proves that under minimum inter-event spacing $\delta > 0$ over lookahead horizon $H \ge 0$,
     any ordered sequence of $N + 1$ scheduled events in $[t_0, t_0 + H]$ satisfies $N \cdot \delta \le H$
     (`minimum_spacing_queue_bound`), whereas without minimum spacing, arbitrarily many future
     events fit inside $(t_0, t_0 + H]$ even when all past events ($t \le t_0$) are pruned (`dense_future_events_in_window`).

Axiom target: Standard Lean axioms only ([propext, Classical.choice, Quot.sound]), 0 sorry.
-/

namespace Research.WorldFrameTransport

noncomputable section

open Set

-- ==============================================================================
-- 1. 3D Vector Geometry
-- ==============================================================================

@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec3

def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def sub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def smul (c : ℝ) (u : Vec3) : Vec3 := ⟨c * u.x, c * u.y, c * u.z⟩
def dot (u v : Vec3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z
def sqNorm (u : Vec3) : ℝ := u.x ^ 2 + u.y ^ 2 + u.z ^ 2
def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

instance : Add Vec3 := ⟨add⟩
instance : Sub Vec3 := ⟨sub⟩
instance : HSMul ℝ Vec3 Vec3 := ⟨smul⟩

@[simp] theorem add_x (u v : Vec3) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : Vec3) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : Vec3) : (u + v).z = u.z + v.z := rfl

@[simp] theorem sub_x (u v : Vec3) : (u - v).x = u.x - v.x := rfl
@[simp] theorem sub_y (u v : Vec3) : (u - v).y = u.y - v.y := rfl
@[simp] theorem sub_z (u v : Vec3) : (u - v).z = u.z - v.z := rfl

@[simp] theorem smul_x (c : ℝ) (u : Vec3) : (c • u).x = c * u.x := rfl
@[simp] theorem smul_y (c : ℝ) (u : Vec3) : (c • u).y = c * u.y := rfl
@[simp] theorem smul_z (c : ℝ) (u : Vec3) : (c • u).z = c * u.z := rfl

@[simp] theorem cross_x (u v : Vec3) : (cross u v).x = u.y * v.z - u.z * v.y := rfl
@[simp] theorem cross_y (u v : Vec3) : (cross u v).y = u.z * v.x - u.x * v.z := rfl
@[simp] theorem cross_z (u v : Vec3) : (cross u v).z = u.x * v.y - u.y * v.x := rfl

end Vec3

-- ==============================================================================
-- 2. Card R06: Rotating-Frame Derivative Transport & Euler–Centripetal Orthogonality
-- ==============================================================================

/-- Euler tangential acceleration α × p = (ddtheta • k_hat) × p. -/
def eulerAccel (k_hat p : Vec3) (ddtheta : ℝ) : Vec3 :=
  Vec3.cross (ddtheta • k_hat) p

/-- Centripetal acceleration ω × (ω × p) = (dtheta • k_hat) × ((dtheta • k_hat) × p). -/
def centripetalAccel (k_hat p : Vec3) (dtheta : ℝ) : Vec3 :=
  Vec3.cross (dtheta • k_hat) (Vec3.cross (dtheta • k_hat) p)

/-- Full world-frame acceleration of a point p = R r_B with body velocity v_B = R ṙ_B
    and body acceleration a_B = R r̈_B on a rotating base:
      a_W = a_B + 2 (ω × v_B) + (α × p) + ω × (ω × p). -/
def worldFrameAccel (a_B v_B k_hat p : Vec3) (dtheta ddtheta : ℝ) : Vec3 :=
  a_B + (2 : ℝ) • Vec3.cross (dtheta • k_hat) v_B +
  eulerAccel k_hat p ddtheta + centripetalAccel k_hat p dtheta

/-- Exact Orthogonality of Euler and Centripetal Accelerations:
    For ANY axis vector k_hat, lever arm p, angular speed dtheta, and angular
    acceleration ddtheta, (α × p) ⬝ (ω × (ω × p)) = 0 identically! -/
theorem euler_centripetal_orthogonal (k_hat p : Vec3) (dtheta ddtheta : ℝ) :
    Vec3.dot (eulerAccel k_hat p ddtheta) (centripetalAccel k_hat p dtheta) = 0 := by
  simp [eulerAccel, centripetalAccel, Vec3.dot]
  ring

/-- Exact Pythagorean Identity for Combined Rotational Transport Acceleration:
    When k_hat is a unit axis (‖k_hat‖² = 1), the squared norm of the combined
    Euler + centripetal acceleration equals:
      ‖α × p + ω × (ω × p)‖² = (ddtheta² + dtheta⁴) * ‖k_hat × p‖²
                              = (ddtheta² + dtheta⁴) * (‖p‖² - (k_hat ⬝ p)²). -/
theorem euler_centripetal_sqNorm_exact (k_hat p : Vec3) (dtheta ddtheta : ℝ)
    (h_unit : Vec3.sqNorm k_hat = 1) :
    Vec3.sqNorm (eulerAccel k_hat p ddtheta + centripetalAccel k_hat p dtheta) =
      (ddtheta ^ 2 + dtheta ^ 4) * Vec3.sqNorm (Vec3.cross k_hat p) ∧
    Vec3.sqNorm (Vec3.cross k_hat p) = Vec3.sqNorm p - (Vec3.dot k_hat p) ^ 2 := by
  have h_id1 : Vec3.sqNorm (eulerAccel k_hat p ddtheta + centripetalAccel k_hat p dtheta) -
      (ddtheta ^ 2 + dtheta ^ 4 * Vec3.sqNorm k_hat) * Vec3.sqNorm (Vec3.cross k_hat p) = 0 := by
    simp [eulerAccel, centripetalAccel, Vec3.sqNorm]
    ring
  rw [h_unit, mul_one] at h_id1
  have h_id2 : Vec3.sqNorm (Vec3.cross k_hat p) -
      (Vec3.sqNorm k_hat * Vec3.sqNorm p - (Vec3.dot k_hat p) ^ 2) = 0 := by
    simp [Vec3.sqNorm, Vec3.dot]
    ring
  rw [h_unit, one_mul] at h_id2
  refine ⟨by linarith, by linarith⟩

/-- Body-Frame Hold Counterexample to Naive Componentwise Acceleration Transfer:
    Even when the robot joint/actuator is completely stationary in the body frame
    (v_B = 0, a_B = 0), base rotation induces world-frame acceleration of squared
    norm (ddtheta² + dtheta⁴) ‖k_hat × p‖², which strictly violates any world-frame
    acceleration bound A_max whenever (ddtheta² + dtheta⁴) ‖k_hat × p‖² > A_max². -/
theorem body_hold_violates_world_accel (k_hat p : Vec3) (dtheta ddtheta A_max : ℝ)
    (h_unit : Vec3.sqNorm k_hat = 1)
    (h_exceed : A_max ^ 2 < (ddtheta ^ 2 + dtheta ^ 4) * Vec3.sqNorm (Vec3.cross k_hat p)) :
    A_max ^ 2 < Vec3.sqNorm (worldFrameAccel ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ k_hat p dtheta ddtheta) := by
  have h_eq : worldFrameAccel ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ k_hat p dtheta ddtheta =
      eulerAccel k_hat p ddtheta + centripetalAccel k_hat p dtheta := by
    ext <;> simp [worldFrameAccel]
  rw [h_eq, (euler_centripetal_sqNorm_exact k_hat p dtheta ddtheta h_unit).1]
  exact h_exceed

-- ==============================================================================
-- 3. Card R07: Minimal-Intervention Nullspace Allocation on Redundant Arms
-- ==============================================================================

/-- Moore–Penrose minimal-intervention joint velocity allocation:
    q* = q_nom + ((v_task - J ⬝ q_nom) / ‖J‖²) • J. -/
def minimalInterventionAlloc (J q_nom : Vec3) (v_task : ℝ) : Vec3 :=
  q_nom + ((v_task - Vec3.dot J q_nom) / Vec3.sqNorm J) • J

/-- 1. Exact Task Fulfillment: J ⬝ q* = v_task whenever ‖J‖² ≠ 0. -/
theorem minimal_intervention_achieves_task (J q_nom : Vec3) (v_task : ℝ)
    (hJ : Vec3.sqNorm J ≠ 0) :
    Vec3.dot J (minimalInterventionAlloc J q_nom v_task) = v_task := by
  have h_alg : Vec3.dot J (minimalInterventionAlloc J q_nom v_task) =
      Vec3.dot J q_nom + ((v_task - Vec3.dot J q_nom) / Vec3.sqNorm J) * Vec3.sqNorm J := by
    simp [minimalInterventionAlloc, Vec3.dot, Vec3.sqNorm]
    ring
  rw [h_alg, div_mul_cancel₀ _ hJ]
  ring

/-- 2. Exact Nullspace Preservation: For ANY posture direction z in the Jacobian nullspace
    (J ⬝ z = 0), the minimal-intervention allocation leaves z ⬝ q_nom completely undisturbed:
      z ⬝ q* = z ⬝ q_nom. -/
theorem minimal_intervention_preserves_nullspace (J q_nom z : Vec3) (v_task : ℝ)
    (hz : Vec3.dot J z = 0) :
    Vec3.dot z (minimalInterventionAlloc J q_nom v_task) = Vec3.dot z q_nom := by
  have h_alg : Vec3.dot z (minimalInterventionAlloc J q_nom v_task) =
      Vec3.dot z q_nom + ((v_task - Vec3.dot J q_nom) / Vec3.sqNorm J) * Vec3.dot J z := by
    simp [minimalInterventionAlloc, Vec3.dot]
    ring
  rw [h_alg, hz, mul_zero, add_zero]

/-- 3. Exact Pythagorean L² Optimality:
    For ANY task-feasible joint velocity q satisfying J ⬝ q = v_task, the squared
    intervention distance from q_nom decomposes orthogonally as:
      ‖q - q_nom‖² = ‖q* - q_nom‖² + ‖q - q*‖²,
    proving that q* uniquely minimizes ‖q - q_nom‖² over the task manifold! -/
theorem minimal_intervention_pythagorean_optimality (J q_nom q : Vec3) (v_task : ℝ)
    (hJ : Vec3.sqNorm J ≠ 0) (hq : Vec3.dot J q = v_task) :
    Vec3.sqNorm (q - q_nom) =
      Vec3.sqNorm (minimalInterventionAlloc J q_nom v_task - q_nom) +
      Vec3.sqNorm (q - minimalInterventionAlloc J q_nom v_task) ∧
    Vec3.sqNorm (minimalInterventionAlloc J q_nom v_task - q_nom) ≤ Vec3.sqNorm (q - q_nom) := by
  set q_star := minimalInterventionAlloc J q_nom v_task
  have h_orth : Vec3.dot (q_star - q_nom) (q - q_star) = 0 := by
    have h_star_task := minimal_intervention_achieves_task J q_nom v_task hJ
    have h_diff_dot : Vec3.dot J (q - q_star) = Vec3.dot J q - Vec3.dot J q_star := by
      simp [Vec3.dot]; ring
    rw [hq, h_star_task, sub_self] at h_diff_dot
    have h_factor : Vec3.dot (q_star - q_nom) (q - q_star) =
        ((v_task - Vec3.dot J q_nom) / Vec3.sqNorm J) * Vec3.dot J (q - q_star) := by
      simp [q_star, minimalInterventionAlloc, Vec3.dot]
      ring
    rw [h_factor, h_diff_dot, mul_zero]
  have h_pyth : Vec3.sqNorm (q - q_nom) =
      Vec3.sqNorm (q_star - q_nom) + Vec3.sqNorm (q - q_star) +
      2 * Vec3.dot (q_star - q_nom) (q - q_star) := by
    simp [Vec3.sqNorm, Vec3.dot]
    ring
  rw [h_orth, mul_zero, add_zero] at h_pyth
  have h_nonneg : 0 ≤ Vec3.sqNorm (q - q_star) := by
    dsimp [Vec3.sqNorm]; positivity
  refine ⟨h_pyth, by linarith⟩

-- ==============================================================================
-- 4. Card R03: Clock-Warp Derivative Chain Rules & Piecewise Slew Velocity Jump
-- ==============================================================================

/-- 1st-Order Clock-Warp Velocity Chain Rule:
    d/dt q(τ(t)) = τ̇(t) * q'(τ(t)). -/
theorem timewarp_velocity_hasDerivAt (q q' tau dtau : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (q' (tau t)) (tau t))
    (htau : HasDerivAt tau (dtau t) t) :
    HasDerivAt (fun s => q (tau s)) (dtau t * q' (tau t)) t := by
  exact (hq.comp t htau).congr_deriv (by ring)

/-- 2nd-Order Clock-Warp Acceleration Chain Rule:
    d²/dt² q(τ(t)) = τ̈(t) * q'(τ(t)) + τ̇(t)² * q''(τ(t)). -/
theorem timewarp_accel_hasDerivAt (q' q'' tau dtau ddtau : ℝ → ℝ) (t : ℝ)
    (hq' : HasDerivAt q' (q'' (tau t)) (tau t))
    (htau : HasDerivAt tau (dtau t) t)
    (hdtau : HasDerivAt dtau (ddtau t) t) :
    HasDerivAt (fun s => dtau s * q' (tau s))
      (ddtau t * q' (tau t) + (dtau t) ^ 2 * q'' (tau t)) t := by
  have h_comp : HasDerivAt (fun s => q' (tau s)) (q'' (tau t) * dtau t) t :=
    hq'.comp t htau
  exact (hdtau.mul h_comp).congr_deriv (by ring)

/-- 3rd-Order Clock-Warp Jerk Chain Rule:
    d³/dt³ q(τ(t)) = τ⃛(t) * q'(τ(t)) + 3 τ̇(t) τ̈(t) * q''(τ(t)) + τ̇(t)³ * q'''(τ(t)). -/
theorem timewarp_jerk_hasDerivAt (q' q'' q''' tau dtau ddtau dddtau : ℝ → ℝ) (t : ℝ)
    (hq' : HasDerivAt q' (q'' (tau t)) (tau t))
    (hq'' : HasDerivAt q'' (q''' (tau t)) (tau t))
    (htau : HasDerivAt tau (dtau t) t)
    (hdtau : HasDerivAt dtau (ddtau t) t)
    (hddtau : HasDerivAt ddtau (dddtau t) t) :
    HasDerivAt (fun s => ddtau s * q' (tau s) + (dtau s) ^ 2 * q'' (tau s))
      (dddtau t * q' (tau t) + 3 * dtau t * ddtau t * q'' (tau t) + (dtau t) ^ 3 * q''' (tau t)) t := by
  have h_comp1 : HasDerivAt (fun s => q' (tau s)) (q'' (tau t) * dtau t) t :=
    hq'.comp t htau
  have h_comp2 : HasDerivAt (fun s => q'' (tau s)) (q''' (tau t) * dtau t) t :=
    hq''.comp t htau
  have h_dtau_sq : HasDerivAt (fun s => (dtau s) ^ 2) (2 * dtau t * ddtau t) t := by
    have h0 := hdtau.pow 2
    exact h0.congr_deriv (by push_cast; ring)
  have h_term1 := hddtau.mul h_comp1
  have h_term2 := h_dtau_sq.mul h_comp2
  exact (h_term1.add h_term2).congr_deriv (by ring)

/-- Four-box reference position spline branch evaluated under clock rate `rate` around t = 0. -/
def splineBranch (rate t : ℝ) : ℝ :=
  ((3 / 2 + 5 * rate * t) ^ 4 - 4 * (3 / 2 + 5 * rate * t - 1) ^ 4) / 1200

/-- Piecewise clock-slewed trajectory: rate 3/2 for t ≤ 0, rate 1/2 for t > 0. -/
def warpedSpline (t : ℝ) : ℝ :=
  if t ≤ 0 then splineBranch (3 / 2) t else splineBranch (1 / 2) t

/-- Exact derivative of splineBranch at t = 0 equals (23 / 480) * rate. -/
theorem splineBranch_hasDerivAt_zero (rate : ℝ) :
    HasDerivAt (splineBranch rate) ((23 / 480) * rate) 0 := by
  have ha : HasDerivAt (fun t : ℝ => 3 / 2 + 5 * rate * t) (5 * rate) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (5 * rate)).const_add (3 / 2)
  have hb := ((ha.pow 4).sub (((ha.sub_const 1).pow 4).const_mul 4)).div_const 1200
  exact hb.congr_deriv (by push_cast; ring)

theorem splineBranches_join : splineBranch (3 / 2) 0 = splineBranch (1 / 2) 0 := by
  dsimp [splineBranch]; norm_num

/-- Complete, Zero-Sorry Proof of R03 Clock-Slew Non-Differentiability:
    Evaluating the smooth C³ four-box position spline across a continuous piecewise-linear
    clock rate change (3/2 to 1/2 at t = 0) destroys differentiability at t = 0,
    inducing an instantaneous velocity jump of -23/480. -/
theorem clock_slew_breaks_spline_differentiability :
    ¬ DifferentiableAt ℝ warpedSpline 0 := by
  have h_left : HasDerivAt (splineBranch (3 / 2)) (23 / 320) 0 :=
    (splineBranch_hasDerivAt_zero (3 / 2)).congr_deriv (by norm_num)
  have h_right : HasDerivAt (splineBranch (1 / 2)) (23 / 960) 0 :=
    (splineBranch_hasDerivAt_zero (1 / 2)).congr_deriv (by norm_num)
  have hl : HasDerivWithinAt warpedSpline (23 / 320) (Iic 0) 0 := by
    apply h_left.hasDerivWithinAt.congr
    · intro t ht
      change t ≤ 0 at ht
      simp [warpedSpline, ht]
    · simp [warpedSpline]
  have hr : HasDerivWithinAt warpedSpline (23 / 960) (Ici 0) 0 := by
    apply h_right.hasDerivWithinAt.congr
    · intro t ht
      by_cases ht0 : t ≤ 0
      · have ht' : t = 0 := le_antisymm ht0 ht
        subst ht'
        simpa [warpedSpline] using splineBranches_join
      · simp [warpedSpline, ht0]
    · simpa [warpedSpline] using splineBranches_join
  intro hd
  have el := UniqueDiffWithinAt.eq_deriv (Iic 0) (uniqueDiffWithinAt_Iic 0)
    hl hd.hasDerivAt.hasDerivWithinAt
  have er := UniqueDiffWithinAt.eq_deriv (Ici 0) (uniqueDiffWithinAt_Ici 0)
    hr hd.hasDerivAt.hasDerivWithinAt
  linarith

-- ==============================================================================
-- 5. Card R05: Retained-History Queue Bounds vs. Pruning-Only Unboundedness
-- ==============================================================================

/-- Minimum-Spacing Retained Queue Bound (Network Calculus Arrival Constraint):
    If an ordered sequence of scheduled event timestamps τ : ℕ → ℝ satisfies
    minimum inter-event spacing τ(k + 1) - τ(k) ≥ δ > 0 and all events through
    index N lie within the lookahead window [τ(0), τ(0) + H], then N * δ ≤ H. -/
theorem minimum_spacing_queue_bound (tau : ℕ → ℝ) (delta H : ℝ)
    (h_spacing : ∀ k, tau k + delta ≤ tau (k + 1)) :
    ∀ N : ℕ, tau 0 + (N : ℝ) * delta ≤ tau N ∧
      (tau N ≤ tau 0 + H → (N : ℝ) * delta ≤ H) := by
  intro N
  have h_ind : tau 0 + (N : ℝ) * delta ≤ tau N := by
    induction N with
    | zero => simp
    | succ n ih =>
      have h_step := h_spacing n
      push_cast
      linarith
  refine ⟨h_ind, fun h_win => by linarith⟩

/-- Pruning-Only Unboundedness Counterexample:
    Without a minimum inter-arrival spacing constraint, for ANY arbitrarily large
    count M ≥ 1 and ANY positive lookahead window H > 0 after current time t₀,
    the geometric sequence of future timestamps t_k = t₀ + H / (k + 1) (for 1 ≤ k ≤ M)
    lies strictly inside the active future window (t₀, t₀ + H] and is strictly
    unnested from completed past events (t ≤ t₀), so pruning past events alone
    cannot bound retained queue memory! -/
theorem dense_future_events_in_window (t0 H : ℝ) (hH : 0 < H) (k : ℕ) (hk : 1 ≤ k) :
    let tk := t0 + H / ((k : ℝ) + 1)
    t0 < tk ∧ tk ≤ t0 + H := by
  intro tk
  have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    linarith
  refine ⟨?_, ?_⟩
  · dsimp [tk]
    have : 0 < H / ((k : ℝ) + 1) := div_pos hH hk_pos
    linarith
  · dsimp [tk]
    have : H / ((k : ℝ) + 1) ≤ H := div_le_self (le_of_lt hH) hk_ge_one
    linarith

#print axioms euler_centripetal_orthogonal
#print axioms euler_centripetal_sqNorm_exact
#print axioms body_hold_violates_world_accel
#print axioms minimal_intervention_achieves_task
#print axioms minimal_intervention_preserves_nullspace
#print axioms minimal_intervention_pythagorean_optimality
#print axioms timewarp_velocity_hasDerivAt
#print axioms timewarp_accel_hasDerivAt
#print axioms timewarp_jerk_hasDerivAt
#print axioms splineBranch_hasDerivAt_zero
#print axioms clock_slew_breaks_spline_differentiability
#print axioms minimum_spacing_queue_bound
#print axioms dense_future_events_in_window

end

end Research.WorldFrameTransport
