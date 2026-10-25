import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Milestone 2 & 3D Centroidal Discharge: Controls — Lorentz-Cone Backup CBF & 4-Contact Dynamics

Formal verification of the closed-form backup Control Barrier Function (CBF)
under second-order Lorentz friction cones, together with the full 3D 4-contact
rectangular-stance Newton–Euler wrench realization, zero 3D angular-momentum drift
($\dot{L} = 0$), and continuous-time Lie-derivative forward invariance discharging `h_margin`.

Author: worker_m2_controls
Axiom target: Standard Lean axioms only ([propext, Classical.choice, Quot.sound]), 0 sorry.
-/

namespace Research.LorentzConeCBF

noncomputable section

/-- A 3D vector with real components. -/
@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec3

def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩
def smul (c : ℝ) (u : Vec3) : Vec3 := ⟨c * u.x, c * u.y, c * u.z⟩
def sub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩
def dot (u v : Vec3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z
def sqNorm (u : Vec3) : ℝ := u.x ^ 2 + u.y ^ 2 + u.z ^ 2
def sqNormXY (u : Vec3) : ℝ := u.x ^ 2 + u.y ^ 2

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

theorem dot_comm (u v : Vec3) : dot u v = dot v u := by
  dsimp [dot]; ring

theorem dot_convex_combination (u v a : Vec3) (lam : ℝ) :
    dot a ((1 - lam) • u + lam • v) = (1 - lam) * dot a u + lam * dot a v := by
  dsimp [dot, smul, add]; ring

/-- 3D Euclidean cross product u × v. -/
def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

@[simp] theorem cross_x (u v : Vec3) : (cross u v).x = u.y * v.z - u.z * v.y := rfl
@[simp] theorem cross_y (u v : Vec3) : (cross u v).y = u.z * v.x - u.x * v.z := rfl
@[simp] theorem cross_z (u v : Vec3) : (cross u v).z = u.x * v.y - u.y * v.x := rfl

theorem dot_cross_self_left (u v : Vec3) : dot u (cross u v) = 0 := by
  dsimp [dot, cross]; ring

theorem dot_cross_self_right (u v : Vec3) : dot v (cross u v) = 0 := by
  dsimp [dot, cross]; ring

end Vec3

/-- Second-order Lorentz friction cone constraint:
    𝒦(μ) = { u ∈ ℝ³ | u₁² + u₂² ≤ μ² u₃², u₃ ≥ 0 }. -/
def LorentzCone (μ : ℝ) : Set Vec3 :=
  { u | u.x ^ 2 + u.y ^ 2 ≤ μ ^ 2 * u.z ^ 2 ∧ 0 ≤ u.z }

/-- Membership predicate for the Lorentz cone. -/
def inLorentzCone (μ : ℝ) (u : Vec3) : Prop :=
  u ∈ LorentzCone μ

/-- Coordinate-wise formulation of the Lorentz cone condition. -/
def inLorentzConeCoords (μ u₁ u₂ u₃ : ℝ) : Prop :=
  u₁ ^ 2 + u₂ ^ 2 ≤ μ ^ 2 * u₃ ^ 2 ∧ 0 ≤ u₃

theorem in_lorentz_cone_coords_iff (μ : ℝ) (u : Vec3) :
    u ∈ LorentzCone μ ↔ inLorentzConeCoords μ u.x u.y u.z :=
  Iff.rfl

/-- Lagrange's algebraic identity in 2D. -/
theorem lagrange_identity_2d (x₁ y₁ x₂ y₂ : ℝ) :
    (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) =
      (x₁ * x₂ + y₁ * y₂) ^ 2 + (x₁ * y₂ - x₂ * y₁) ^ 2 := by
  ring

/-- Cauchy-Schwarz inequality in 2D derived algebraically. -/
theorem cauchy_schwarz_2d (x₁ y₁ x₂ y₂ : ℝ) :
    (x₁ * x₂ + y₁ * y₂) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) := by
  have h := lagrange_identity_2d x₁ y₁ x₂ y₂
  have hsq : 0 ≤ (x₁ * y₂ - x₂ * y₁) ^ 2 := sq_nonneg _
  linarith

/-- Cross-term bound between two vectors inside the Lorentz friction cone. -/
theorem lorentz_cross_term_le (μ : ℝ) (_hμ : 0 ≤ μ) (u₁ u₂ : Vec3)
    (h₁ : u₁ ∈ LorentzCone μ) (h₂ : u₂ ∈ LorentzCone μ) :
    u₁.x * u₂.x + u₁.y * u₂.y ≤ μ ^ 2 * u₁.z * u₂.z := by
  rcases h₁ with ⟨h₁_cone, h₁_z⟩
  rcases h₂ with ⟨h₂_cone, h₂_z⟩
  have hcs := cauchy_schwarz_2d u₁.x u₁.y u₂.x u₂.y
  have h_u1_sq : 0 ≤ u₁.x ^ 2 + u₁.y ^ 2 := by positivity
  have h_u2_sq : 0 ≤ u₂.x ^ 2 + u₂.y ^ 2 := by positivity
  have h_prod : (u₁.x ^ 2 + u₁.y ^ 2) * (u₂.x ^ 2 + u₂.y ^ 2) ≤
      (μ ^ 2 * u₁.z ^ 2) * (μ ^ 2 * u₂.z ^ 2) := by
    nlinarith
  have h_sq_bound : (u₁.x * u₂.x + u₁.y * u₂.y) ^ 2 ≤ (μ ^ 2 * u₁.z * u₂.z) ^ 2 := by
    have h_id : (μ ^ 2 * u₁.z ^ 2) * (μ ^ 2 * u₂.z ^ 2) = (μ ^ 2 * u₁.z * u₂.z) ^ 2 := by ring
    linarith
  have h_rhs_nonneg : 0 ≤ μ ^ 2 * u₁.z * u₂.z := by positivity
  by_contra h_neg
  have h_gt : μ ^ 2 * u₁.z * u₂.z < u₁.x * u₂.x + u₁.y * u₂.y := not_le.mp h_neg
  have h_diff_pos : 0 < (u₁.x * u₂.x + u₁.y * u₂.y) - μ ^ 2 * u₁.z * u₂.z := by linarith
  have h_sum_pos : 0 < (u₁.x * u₂.x + u₁.y * u₂.y) + μ ^ 2 * u₁.z * u₂.z := by linarith
  have h_prod_pos : 0 < ((u₁.x * u₂.x + u₁.y * u₂.y) - μ ^ 2 * u₁.z * u₂.z) *
      ((u₁.x * u₂.x + u₁.y * u₂.y) + μ ^ 2 * u₁.z * u₂.z) := mul_pos h_diff_pos h_sum_pos
  have h_ring : ((u₁.x * u₂.x + u₁.y * u₂.y) - μ ^ 2 * u₁.z * u₂.z) *
      ((u₁.x * u₂.x + u₁.y * u₂.y) + μ ^ 2 * u₁.z * u₂.z) =
      (u₁.x * u₂.x + u₁.y * u₂.y) ^ 2 - (μ ^ 2 * u₁.z * u₂.z) ^ 2 := by ring
  linarith

/-- Convex combination invariance of the Lorentz friction cone:
    If u₁, u₂ ∈ 𝒦(μ) and lam ∈ [0, 1], then (1 - lam) u₁ + lam u₂ ∈ 𝒦(μ). -/
theorem lorentz_convex_combination (μ : ℝ) (hμ : 0 ≤ μ) (u₁ u₂ : Vec3)
    (h₁ : u₁ ∈ LorentzCone μ) (h₂ : u₂ ∈ LorentzCone μ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ((1 - lam) • u₁ + lam • u₂) ∈ LorentzCone μ := by
  rcases h₁ with ⟨h₁_cone, h₁_z⟩
  rcases h₂ with ⟨h₂_cone, h₂_z⟩
  have h_cross := lorentz_cross_term_le μ hμ u₁ u₂ ⟨h₁_cone, h₁_z⟩ ⟨h₂_cone, h₂_z⟩
  refine ⟨?_, ?_⟩
  · have h_decomp : μ ^ 2 * ((1 - lam) * u₁.z + lam * u₂.z) ^ 2 -
        (((1 - lam) * u₁.x + lam * u₂.x) ^ 2 + ((1 - lam) * u₁.y + lam * u₂.y) ^ 2) =
        (1 - lam) ^ 2 * (μ ^ 2 * u₁.z ^ 2 - (u₁.x ^ 2 + u₁.y ^ 2)) +
        lam ^ 2 * (μ ^ 2 * u₂.z ^ 2 - (u₂.x ^ 2 + u₂.y ^ 2)) +
        2 * (1 - lam) * lam * (μ ^ 2 * u₁.z * u₂.z - (u₁.x * u₂.x + u₁.y * u₂.y)) := by
      ring
    have term1 : 0 ≤ (1 - lam) ^ 2 * (μ ^ 2 * u₁.z ^ 2 - (u₁.x ^ 2 + u₁.y ^ 2)) := by
      have : 0 ≤ μ ^ 2 * u₁.z ^ 2 - (u₁.x ^ 2 + u₁.y ^ 2) := by linarith
      positivity
    have term2 : 0 ≤ lam ^ 2 * (μ ^ 2 * u₂.z ^ 2 - (u₂.x ^ 2 + u₂.y ^ 2)) := by
      have : 0 ≤ μ ^ 2 * u₂.z ^ 2 - (u₂.x ^ 2 + u₂.y ^ 2) := by linarith
      positivity
    have term3 : 0 ≤ 2 * (1 - lam) * lam * (μ ^ 2 * u₁.z * u₂.z - (u₁.x * u₂.x + u₁.y * u₂.y)) := by
      have : 0 ≤ μ ^ 2 * u₁.z * u₂.z - (u₁.x * u₂.x + u₁.y * u₂.y) := by linarith
      positivity
    have h_diff_nonneg : 0 ≤ μ ^ 2 * ((1 - lam) * u₁.z + lam * u₂.z) ^ 2 -
        (((1 - lam) * u₁.x + lam * u₂.x) ^ 2 + ((1 - lam) * u₁.y + lam * u₂.y) ^ 2) := by
      linarith
    dsimp [Vec3.smul, Vec3.add]
    linarith
  · dsimp [Vec3.smul, Vec3.add]
    positivity

/-- Stopping-distance backup Control Barrier Function:
    h_b(r, v) = (r_limit - r) ⬝ n_hat - ||v||² / (2 * a_brake). -/
def backupCBF (r_limit r v n_hat : Vec3) (a_brake : ℝ) : ℝ :=
  Vec3.dot (r_limit - r) n_hat - Vec3.sqNorm v / (2 * a_brake)

/-- Positive stopping barrier implies position clearance when stopped (v = 0). -/
theorem backup_cbf_safe_at_rest (r_limit r n_hat : Vec3) (a_brake : ℝ)
    (zero_vel : Vec3) (h_zero : zero_vel = ⟨0, 0, 0⟩)
    (h_safe : 0 ≤ backupCBF r_limit r zero_vel n_hat a_brake) :
    0 ≤ Vec3.dot (r_limit - r) n_hat := by
  subst h_zero
  dsimp [backupCBF, Vec3.sqNorm] at h_safe
  have h_zero_norm : (0 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2 = 0 := by ring
  rw [h_zero_norm, zero_div, sub_zero] at h_safe
  exact h_safe

/-- Velocity norm bound guaranteed by the backup barrier. -/
theorem backup_cbf_velocity_bound (r_limit r v n_hat : Vec3) (a_brake : ℝ)
    (ha : 0 < a_brake) (h_safe : 0 ≤ backupCBF r_limit r v n_hat a_brake) :
    Vec3.sqNorm v ≤ 2 * a_brake * Vec3.dot (r_limit - r) n_hat := by
  dsimp [backupCBF] at h_safe
  have h2a : 0 < 2 * a_brake := by linarith
  have h_le : Vec3.sqNorm v / (2 * a_brake) ≤ Vec3.dot (r_limit - r) n_hat := by linarith
  have h_mul := (div_le_iff₀ h2a).mp h_le
  nlinarith

/-- Closed-form interpolation parameter:
    λ*(x) = max(0, (b - a_nom) / (a_pi - a_nom)). -/
def lambda_star (b a_nom a_pi : ℝ) : ℝ :=
  max 0 ((b - a_nom) / (a_pi - a_nom))

/-- Interpolated control vector between nominal and backup allocations. -/
def interpolatedControl (u_nom pi_b : Vec3) (lam : ℝ) : Vec3 :=
  (1 - lam) • u_nom + lam • pi_b

/-- The interpolation parameter is always non-negative. -/
theorem lambda_star_nonneg (b a_nom a_pi : ℝ) :
    0 ≤ lambda_star b a_nom a_pi :=
  le_max_left 0 _

/-- When the backup policy has positive margin over the barrier requirement (b ≤ a_pi)
    and authority over nominal (a_nom < a_pi), λ* is bounded above by 1. -/
theorem lambda_star_le_one (b a_nom a_pi : ℝ)
    (h_denom : 0 < a_pi - a_nom) (h_margin : b ≤ a_pi) :
    lambda_star b a_nom a_pi ≤ 1 := by
  dsimp [lambda_star]
  apply max_le
  · linarith
  · rw [div_le_iff₀ h_denom]
    linarith

/-- When nominal already satisfies the CBF condition (b ≤ a_nom), λ* = 0. -/
theorem lambda_star_eq_zero_of_safe (b a_nom a_pi : ℝ)
    (h_denom : 0 < a_pi - a_nom) (h_safe : b ≤ a_nom) :
    lambda_star b a_nom a_pi = 0 := by
  dsimp [lambda_star]
  have h_div_nonpos : (b - a_nom) / (a_pi - a_nom) ≤ 0 := by
    have h_num : b - a_nom ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h_num (le_of_lt h_denom)
  exact max_eq_left h_div_nonpos

/-- When nominal violates the CBF condition (a_nom < b), λ* equals the exact ratio. -/
theorem lambda_star_eq_ratio_of_violation (b a_nom a_pi : ℝ)
    (h_denom : 0 < a_pi - a_nom) (h_viol : a_nom < b) :
    lambda_star b a_nom a_pi = (b - a_nom) / (a_pi - a_nom) := by
  dsimp [lambda_star]
  have h_div_pos : 0 < (b - a_nom) / (a_pi - a_nom) := by
    have h_num : 0 < b - a_nom := by linarith
    exact div_pos h_num h_denom
  exact max_eq_right (le_of_lt h_div_pos)

/-- The closed-form interpolation satisfies the scalar barrier condition b ≤ a(x)ᵀ u(λ*). -/
theorem interpolation_satisfies_barrier (b a_nom a_pi : ℝ)
    (h_denom : 0 < a_pi - a_nom) (_h_margin : b ≤ a_pi) :
    b ≤ (1 - lambda_star b a_nom a_pi) * a_nom + (lambda_star b a_nom a_pi) * a_pi := by
  rcases lt_or_ge a_nom b with h_lt | h_ge
  · rw [lambda_star_eq_ratio_of_violation b a_nom a_pi h_denom h_lt]
    have h_ne : a_pi - a_nom ≠ 0 := ne_of_gt h_denom
    have h_calc : (1 - (b - a_nom) / (a_pi - a_nom)) * a_nom +
        ((b - a_nom) / (a_pi - a_nom)) * a_pi = b := by
      calc
        (1 - (b - a_nom) / (a_pi - a_nom)) * a_nom + ((b - a_nom) / (a_pi - a_nom)) * a_pi
        _ = a_nom + ((b - a_nom) / (a_pi - a_nom)) * (a_pi - a_nom) := by ring
        _ = a_nom + (b - a_nom) := by rw [div_mul_cancel₀ (b - a_nom) h_ne]
        _ = b := by ring
    linarith
  · rw [lambda_star_eq_zero_of_safe b a_nom a_pi h_denom h_ge]
    linarith

/-- Master Theorem: The Lorentz-Cone Optimally Interpolated Controller
    simultaneously satisfies:
    1. Friction cone admissibility: u*(x) ∈ 𝒦(μ).
    2. Control Barrier Function condition: a(x) ⬝ u*(x) ≥ b(x). -/
theorem lorentz_backup_controller_safe (μ : ℝ) (hμ : 0 ≤ μ)
    (a_cbf : Vec3) (b : ℝ) (u_nom pi_b : Vec3)
    (hu : u_nom ∈ LorentzCone μ) (hp : pi_b ∈ LorentzCone μ)
    (h_denom : Vec3.dot a_cbf u_nom < Vec3.dot a_cbf pi_b)
    (h_margin : b ≤ Vec3.dot a_cbf pi_b) :
    let lam := lambda_star b (Vec3.dot a_cbf u_nom) (Vec3.dot a_cbf pi_b)
    let u_safe := interpolatedControl u_nom pi_b lam
    u_safe ∈ LorentzCone μ ∧ b ≤ Vec3.dot a_cbf u_safe := by
  intro lam u_safe
  have h_diff_pos : 0 < Vec3.dot a_cbf pi_b - Vec3.dot a_cbf u_nom := by linarith
  have hlam0 : 0 ≤ lam := lambda_star_nonneg b (Vec3.dot a_cbf u_nom) (Vec3.dot a_cbf pi_b)
  have hlam1 : lam ≤ 1 := lambda_star_le_one b (Vec3.dot a_cbf u_nom) (Vec3.dot a_cbf pi_b) h_diff_pos h_margin
  have h_cone : u_safe ∈ LorentzCone μ := by
    dsimp [u_safe, interpolatedControl]
    exact lorentz_convex_combination μ hμ u_nom pi_b hu hp lam hlam0 hlam1
  have h_cbf : b ≤ Vec3.dot a_cbf u_safe := by
    dsimp [u_safe, interpolatedControl]
    rw [Vec3.dot_convex_combination]
    exact interpolation_satisfies_barrier b (Vec3.dot a_cbf u_nom) (Vec3.dot a_cbf pi_b) h_diff_pos h_margin
  exact ⟨h_cone, h_cbf⟩

-- ==============================================================================
-- 2. 3D 4-Contact Centroidal Newton–Euler Wrench & Zero Angular Momentum Drift
-- ==============================================================================

/-- Physical parameters for a 3D rigid-body robot over a 4-contact rectangular stance
    [-Wx, Wx] × [-Wy, Wy] at CoM height hG > 0. -/
structure CentroidalQuadParams where
  m : ℝ
  g : ℝ
  hG : ℝ
  Wx : ℝ
  Wy : ℝ
  mu : ℝ
  hm : 0 < m
  hg : 0 < g
  hhG : 0 < hG
  hWx : 0 < Wx
  hWy : 0 < Wy
  hmu : 0 ≤ mu

/-- Contact position vector relative to CoM for corner signs (ex, ey) ∈ {-1, +1}². -/
def quadContactOffset (p : CentroidalQuadParams) (ex ey : ℝ) : Vec3 :=
  ⟨ex * p.Wx, ey * p.Wy, -p.hG⟩

/-- Bilinear ZMP normal contact force at corner (ex, ey) ∈ {-1, +1}² for horizontal
    CoM acceleration (ax, ay). -/
def quadNormalForce (p : CentroidalQuadParams) (ax ay ex ey : ℝ) : ℝ :=
  (p.m * p.g / 4) * (1 - ex * (p.hG * ax) / (p.g * p.Wx)) * (1 - ey * (p.hG * ay) / (p.g * p.Wy))

/-- 3D contact force vector at corner (ex, ey) ∈ {-1, +1}² using proportional
    tangential friction allocation: fx = (ax/g) fz, fy = (ay/g) fz. -/
def quadContactForce (p : CentroidalQuadParams) (ax ay ex ey : ℝ) : Vec3 :=
  let fz := quadNormalForce p ax ay ex ey
  ⟨(ax / p.g) * fz, (ay / p.g) * fz, fz⟩

/-- Exact 3D Newton Translational Realization:
    Summing the 4 corner contact forces minus gravity (0, 0, m g) produces the exact
    desired 3D centroidal translational wrench (m ax, m ay, 0). -/
theorem quad_contact_net_force (p : CentroidalQuadParams) (ax ay : ℝ) :
    quadContactForce p ax ay (-1) (-1) + quadContactForce p ax ay (-1) 1 +
    quadContactForce p ax ay 1 (-1) + quadContactForce p ax ay 1 1 -
    ⟨0, 0, p.m * p.g⟩ = ⟨p.m * ax, p.m * ay, 0⟩ := by
  have hg : p.g ≠ 0 := ne_of_gt p.hg
  have hWx : p.Wx ≠ 0 := ne_of_gt p.hWx
  have hWy : p.Wy ≠ 0 := ne_of_gt p.hWy
  ext <;> {
    dsimp [quadContactForce, quadNormalForce, Vec3.add, Vec3.sub]
    field_simp
    ring
  }

/-- Exact 3D Euler Rotational Equilibrium (Zero Angular Momentum Drift):
    Under the bilinear ZMP normal load and proportional tangential force allocation,
    the net 3D centroidal torque L̇ = ∑_{i=1}^4 (p_i - r_CoM) × f_i vanishes
    identically across ALL THREE AXES (roll L̇_x = 0, pitch L̇_y = 0, AND yaw L̇_z = 0). -/
theorem quad_contact_zero_angular_momentum (p : CentroidalQuadParams) (ax ay : ℝ) :
    Vec3.cross (quadContactOffset p (-1) (-1)) (quadContactForce p ax ay (-1) (-1)) +
    Vec3.cross (quadContactOffset p (-1) 1) (quadContactForce p ax ay (-1) 1) +
    Vec3.cross (quadContactOffset p 1 (-1)) (quadContactForce p ax ay 1 (-1)) +
    Vec3.cross (quadContactOffset p 1 1) (quadContactForce p ax ay 1 1) = ⟨0, 0, 0⟩ := by
  have hg : p.g ≠ 0 := ne_of_gt p.hg
  have hWx : p.Wx ≠ 0 := ne_of_gt p.hWx
  have hWy : p.Wy ≠ 0 := ne_of_gt p.hWy
  ext <;> {
    dsimp [Vec3.cross, quadContactOffset, quadContactForce, quadNormalForce, Vec3.add]
    field_simp
    ring
  }

/-- Individual contact force at corner (ex, ey) ∈ {-1, 1}² lies inside the 3D Lorentz
    friction cone 𝒦(μ) whenever the 2D ZMP rectangular bounds |ax| ≤ g Wx / hG,
    |ay| ≤ g Wy / hG and the friction disk bound ax² + ay² ≤ (μ g)² hold. -/
theorem quad_contact_in_lorentz_cone (p : CentroidalQuadParams) (ax ay ex ey : ℝ)
    (hex : ex = -1 ∨ ex = 1) (hey : ey = -1 ∨ ey = 1)
    (h_zmp_x : p.hG * |ax| ≤ p.g * p.Wx)
    (h_zmp_y : p.hG * |ay| ≤ p.g * p.Wy)
    (h_fric : ax ^ 2 + ay ^ 2 ≤ (p.mu * p.g) ^ 2) :
    quadContactForce p ax ay ex ey ∈ LorentzCone p.mu := by
  have hg_pos : 0 < p.g := p.hg
  have hgWx_pos : 0 < p.g * p.Wx := mul_pos p.hg p.hWx
  have hgWy_pos : 0 < p.g * p.Wy := mul_pos p.hg p.hWy
  have hax_le : ax ≤ |ax| := le_abs_self ax
  have hax_ge : -|ax| ≤ ax := neg_abs_le ax
  have hay_le : ay ≤ |ay| := le_abs_self ay
  have hay_ge : -|ay| ≤ ay := neg_abs_le ay
  have hhG_pos : 0 < p.hG := p.hhG
  have h_num_x : ex * (p.hG * ax) ≤ p.g * p.Wx := by
    rcases hex with rfl | rfl <;> nlinarith
  have h_num_y : ey * (p.hG * ay) ≤ p.g * p.Wy := by
    rcases hey with rfl | rfl <;> nlinarith
  have h_fx_nonneg : 0 ≤ 1 - ex * (p.hG * ax) / (p.g * p.Wx) := by
    have h_div : ex * (p.hG * ax) / (p.g * p.Wx) ≤ 1 :=
      (div_le_iff₀ hgWx_pos).mpr (by linarith)
    linarith
  have h_fy_nonneg : 0 ≤ 1 - ey * (p.hG * ay) / (p.g * p.Wy) := by
    have h_div : ey * (p.hG * ay) / (p.g * p.Wy) ≤ 1 :=
      (div_le_iff₀ hgWy_pos).mpr (by linarith)
    linarith
  have h_fz_nonneg : 0 ≤ quadNormalForce p ax ay ex ey := by
    dsimp [quadNormalForce]
    have hm_pos : 0 ≤ p.m * p.g / 4 :=
      div_nonneg (mul_nonneg (le_of_lt p.hm) (le_of_lt p.hg)) (by norm_num)
    exact mul_nonneg (mul_nonneg hm_pos h_fx_nonneg) h_fy_nonneg
  refine ⟨?_, h_fz_nonneg⟩
  dsimp [quadContactForce]
  set fz := quadNormalForce p ax ay ex ey
  have h_factor : ((ax / p.g) * fz) ^ 2 + ((ay / p.g) * fz) ^ 2 =
      ((ax ^ 2 + ay ^ 2) / p.g ^ 2) * fz ^ 2 := by ring
  rw [h_factor]
  have h_div_le : (ax ^ 2 + ay ^ 2) / p.g ^ 2 ≤ p.mu ^ 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hg_pos)]
    nlinarith
  exact mul_le_mul_of_nonneg_right h_div_le (sq_nonneg fz)

-- ==============================================================================
-- 3. Continuous-Time 3D Lie Derivative & Forward Invariance (Discharging h_margin)
-- ==============================================================================

/-- Directional stopping-distance Control Barrier Function along unit normal n_hat:
    h_dir(r, v) = (r_limit - r) ⬝ n_hat - (v ⬝ n_hat)² / (2 a_brake). -/
def directionalCBF (r_limit r v n_hat : Vec3) (a_brake : ℝ) : ℝ :=
  Vec3.dot (r_limit - r) n_hat - (Vec3.dot v n_hat) ^ 2 / (2 * a_brake)

/-- Exact Continuous-Time Lie Derivative of the 3D Directional Stopping CBF:
    Along any differentiable 3D trajectory (r(t), v(t)) with ṙ(t) = v(t) and v̇(t) = a(t),
    the barrier time derivative equals:
      d/dt h_dir(r(t), v(t)) = -(v(t) ⬝ n_hat) - (v(t) ⬝ n_hat)(a(t) ⬝ n_hat) / a_brake. -/
theorem directional_cbf_hasDerivAt (r_limit n_hat : Vec3) (a_brake : ℝ)
    (r v a : ℝ → Vec3) (t : ℝ)
    (hrx : HasDerivAt (fun s => (r s).x) (v t).x t)
    (hry : HasDerivAt (fun s => (r s).y) (v t).y t)
    (hrz : HasDerivAt (fun s => (r s).z) (v t).z t)
    (hvx : HasDerivAt (fun s => (v s).x) (a t).x t)
    (hvy : HasDerivAt (fun s => (v s).y) (a t).y t)
    (hvz : HasDerivAt (fun s => (v s).z) (a t).z t) :
    HasDerivAt (fun s => directionalCBF r_limit (r s) (v s) n_hat a_brake)
      (-(Vec3.dot (v t) n_hat) - (Vec3.dot (v t) n_hat) * (Vec3.dot (a t) n_hat) / a_brake) t := by
  have h_pos_dot : HasDerivAt (fun s => Vec3.dot (r_limit - r s) n_hat)
      (-(Vec3.dot (v t) n_hat)) t := by
    have h1 := ((hasDerivAt_const t r_limit.x).sub hrx).mul_const n_hat.x
    have h2 := ((hasDerivAt_const t r_limit.y).sub hry).mul_const n_hat.y
    have h3 := ((hasDerivAt_const t r_limit.z).sub hrz).mul_const n_hat.z
    exact ((h1.add h2).add h3).congr_deriv (by dsimp [Vec3.dot]; ring)
  have h_vel_dot : HasDerivAt (fun s => Vec3.dot (v s) n_hat) (Vec3.dot (a t) n_hat) t := by
    have h1 := hvx.mul_const n_hat.x
    have h2 := hvy.mul_const n_hat.y
    have h3 := hvz.mul_const n_hat.z
    exact (h1.add h2).add h3
  have h_vel_sq : HasDerivAt (fun s => (Vec3.dot (v s) n_hat) ^ 2 / (2 * a_brake))
      ((Vec3.dot (v t) n_hat) * (Vec3.dot (a t) n_hat) / a_brake) t := by
    have h_pow := (h_vel_dot.pow 2).div_const (2 * a_brake)
    exact h_pow.congr_deriv (by push_cast; ring)
  exact h_pos_dot.sub h_vel_sq

/-- First-Principles Discharge of `h_margin`:
    When the backup emergency braking acceleration is pi_b = (-a_brake) • n_hat
    along a unit normal n_hat (‖n_hat‖² = 1), its barrier inner product against
    a_cbf = -n_hat equals a_brake identically, discharging `b ≤ a_cbf ⬝ pi_b`
    for `b = a_brake` with ZERO assumed slack! -/
theorem backup_braking_discharges_margin (n_hat : Vec3) (a_brake : ℝ)
    (h_unit : Vec3.sqNorm n_hat = 1) :
    let a_cbf := (-1 : ℝ) • n_hat
    let pi_b := (-a_brake) • n_hat
    a_brake ≤ Vec3.dot a_cbf pi_b := by
  intro a_cbf pi_b
  have h_eq : Vec3.dot a_cbf pi_b = a_brake * Vec3.sqNorm n_hat := by
    dsimp [a_cbf, pi_b, Vec3.dot, Vec3.smul, Vec3.sqNorm]
    ring
  rw [h_eq, h_unit, mul_one]

/-- Unconditional Continuous-Time Forward Invariance of the 3D Stopping CBF:
    If the initial state satisfies h_dir(r(0), v(0)) ≥ 0 and at every time t ≥ 0
    the closed-loop acceleration satisfies the Lie derivative barrier condition
    -(v(t) ⬝ n_hat) - (v(t) ⬝ n_hat)(a(t) ⬝ n_hat) / a_brake ≥ 0,
    then h_dir(r(t), v(t)) ≥ 0 and (r_limit - r(t)) ⬝ n_hat ≥ 0 for ALL t ≥ 0. -/
theorem centroidal_cbf_forward_invariant (r_limit n_hat : Vec3) (a_brake : ℝ)
    (ha : 0 < a_brake) (r v a : ℝ → Vec3)
    (hrx : ∀ t, 0 ≤ t → HasDerivAt (fun s => (r s).x) (v t).x t)
    (hry : ∀ t, 0 ≤ t → HasDerivAt (fun s => (r s).y) (v t).y t)
    (hrz : ∀ t, 0 ≤ t → HasDerivAt (fun s => (r s).z) (v t).z t)
    (hvx : ∀ t, 0 ≤ t → HasDerivAt (fun s => (v s).x) (a t).x t)
    (hvy : ∀ t, 0 ≤ t → HasDerivAt (fun s => (v s).y) (a t).y t)
    (hvz : ∀ t, 0 ≤ t → HasDerivAt (fun s => (v s).z) (a t).z t)
    (h_init : 0 ≤ directionalCBF r_limit (r 0) (v 0) n_hat a_brake)
    (h_lie : ∀ t, 0 ≤ t →
      0 ≤ -(Vec3.dot (v t) n_hat) - (Vec3.dot (v t) n_hat) * (Vec3.dot (a t) n_hat) / a_brake) :
    ∀ t, 0 ≤ t →
      0 ≤ directionalCBF r_limit (r t) (v t) n_hat a_brake ∧
      0 ≤ Vec3.dot (r_limit - r t) n_hat := by
  have hd : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => directionalCBF r_limit (r s) (v s) n_hat a_brake)
        (-(Vec3.dot (v t) n_hat) - (Vec3.dot (v t) n_hat) * (Vec3.dot (a t) n_hat) / a_brake) t :=
    fun t ht => directional_cbf_hasDerivAt r_limit n_hat a_brake r v a t
      (hrx t ht) (hry t ht) (hrz t ht) (hvx t ht) (hvy t ht) (hvz t ht)
  have hm : MonotoneOn (fun s => directionalCBF r_limit (r s) (v s) n_hat a_brake) (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Set.mem_of_mem_of_subset hs interior_subset)).hasDerivWithinAt)
      (fun s hs => h_lie s (Set.mem_of_mem_of_subset hs interior_subset))
  intro t ht
  have h_ge : directionalCBF r_limit (r 0) (v 0) n_hat a_brake ≤
      directionalCBF r_limit (r t) (v t) n_hat a_brake :=
    hm (by simp) ht ht
  have h_cbf_t : 0 ≤ directionalCBF r_limit (r t) (v t) n_hat a_brake := le_trans h_init h_ge
  refine ⟨h_cbf_t, ?_⟩
  dsimp [directionalCBF] at h_cbf_t
  have h_sq_div : 0 ≤ (Vec3.dot (v t) n_hat) ^ 2 / (2 * a_brake) :=
    div_nonneg (sq_nonneg _) (by linarith)
  linarith

#print axioms lagrange_identity_2d
#print axioms cauchy_schwarz_2d
#print axioms lorentz_cross_term_le
#print axioms lorentz_convex_combination
#print axioms backup_cbf_safe_at_rest
#print axioms backup_cbf_velocity_bound
#print axioms lambda_star_nonneg
#print axioms lambda_star_le_one
#print axioms lambda_star_eq_zero_of_safe
#print axioms lambda_star_eq_ratio_of_violation
#print axioms interpolation_satisfies_barrier
#print axioms lorentz_backup_controller_safe
#print axioms quad_contact_net_force
#print axioms quad_contact_zero_angular_momentum
#print axioms quad_contact_in_lorentz_cone
#print axioms directional_cbf_hasDerivAt
#print axioms backup_braking_discharges_margin
#print axioms centroidal_cbf_forward_invariant

end

end Research.LorentzConeCBF
