import Mathlib

/-!
# Planar robot kinematics

This file develops elementary planar robot kinematics, culminating in a rigorous
treatment of the group `SE(2)` of orientation-preserving rigid motions inside Mathlib's
`E(2) := ℝ² ≃ᵃⁱ[ℝ] ℝ²`.

## Main results

* `Pose` : planar poses `(θ, p)` with `θ : Real.Angle`, `p : ℂ ≅ ℝ²`, the group law
  `(θ₁,p₁)(θ₂,p₂) = (θ₁+θ₂, p₁ + R(θ₁) p₂)`, a `Group` instance, a `MulAction` on the plane,
  and `Pose.dist_smul` (rigid motions preserve distances).
* `SE2` : the subgroup of `E(2)` with linear part of determinant `1`;
  `mem_SE2_iff` (every element is a rotation followed by a translation),
  `isClopen_SE2`, and the key theorem `path_mem_SE2`: a continuous path `m : I → E(2)` with
  `m 0 = id` stays in `SE2`. This makes rigorous the justification in the formal-conjectures
  formalisation of the moving sofa problem
  ("we use E(2) and rely on continuity and m(0) = id to ensure m is in SE(2)"),
  using the very same topology on `E(2)`.
* `Unicycle` : explicit solutions of `ẋ = v cos θ, ẏ = v sin θ, θ̇ = ω`, the circular-arc case
  (`ω ≠ 0`, radius `|v/ω|`) and the straight-line case (`ω = 0`).
* `TwoLink` : forward kinematics of a two-link planar arm, `‖p‖² = l₁² + l₂² + 2 l₁ l₂ cos q₂`,
  the workspace is exactly the closed annulus `|l₁ - l₂| ≤ ‖p‖ ≤ l₁ + l₂` (`range_fk`),
  Jacobian determinant `l₁ l₂ sin q₂`, and singularities = workspace boundary.
* `DiffDrive` : the linear bijection between wheel speeds and body twist `(v, ω)`.
-/

namespace RoboLean.Kinematics

open scoped unitInterval

/-! ## 1. Planar poses as a group acting on the plane

We model the plane as `ℂ` (which carries the Euclidean metric) and represent the rotation
`R(θ)` as multiplication by the unit complex number `e^{iθ}`. Coordinate formulas in terms of
`cos θ`, `sin θ` are given by `Pose.smul_re` and `Pose.smul_im`. -/

/-- A planar pose: heading `θ` and position `p` (the plane is identified with `ℂ`). -/
@[ext] structure Pose where
  θ : Real.Angle
  p : ℂ

namespace Pose

/-- The rotation `R(θ)`, as the unit complex number `e^{iθ}`. -/
noncomputable def rot (θ : Real.Angle) : ℂ := (θ.toCircle : ℂ)

@[simp] lemma rot_zero : rot 0 = 1 := by simp [rot]
lemma rot_add (a b : Real.Angle) : rot (a + b) = rot a * rot b := by
  simp [rot, Real.Angle.toCircle_add]
@[simp] lemma norm_rot (a : Real.Angle) : ‖rot a‖ = 1 := Circle.norm_coe _
lemma rot_neg_mul (a : Real.Angle) : rot (-a) * rot a = 1 := by
  rw [← rot_add]; simp
lemma rot_re (a : Real.Angle) : (rot a).re = a.cos := by simp [rot, Real.Angle.coe_toCircle]
lemma rot_im (a : Real.Angle) : (rot a).im = a.sin := by simp [rot, Real.Angle.coe_toCircle]

/-- Pose composition `(θ₁,p₁)*(θ₂,p₂) = (θ₁+θ₂, p₁ + R(θ₁) p₂)`. -/
noncomputable instance : Mul Pose := ⟨fun a b => ⟨a.θ + b.θ, a.p + rot a.θ * b.p⟩⟩
noncomputable instance : One Pose := ⟨⟨0, 0⟩⟩
noncomputable instance : Inv Pose := ⟨fun a => ⟨-a.θ, -(rot (-a.θ) * a.p)⟩⟩

@[simp] lemma mul_θ (a b : Pose) : (a * b).θ = a.θ + b.θ := rfl
@[simp] lemma mul_p (a b : Pose) : (a * b).p = a.p + rot a.θ * b.p := rfl
@[simp] lemma one_θ : (1 : Pose).θ = 0 := rfl
@[simp] lemma one_p : (1 : Pose).p = 0 := rfl
@[simp] lemma inv_θ (a : Pose) : a⁻¹.θ = -a.θ := rfl
@[simp] lemma inv_p (a : Pose) : a⁻¹.p = -(rot (-a.θ) * a.p) := rfl

/-- Planar poses form a group (`SE(2)` in coordinates). -/
noncomputable instance : Group Pose where
  mul_assoc a b c := by
    ext
    · simp [add_assoc]
    · simp [rot_add]; ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    ext
    · simp
    · simp

/-- A pose acts on points of the plane by `g • z = R(θ) z + p`. -/
noncomputable instance : MulAction Pose ℂ where
  smul g z := rot g.θ * z + g.p
  one_smul z := by show rot 0 * z + 0 = z; simp
  mul_smul a b z := by
    show rot (a.θ + b.θ) * z + (a.p + rot a.θ * b.p) = rot a.θ * (rot b.θ * z + b.p) + a.p
    rw [rot_add]; ring

lemma smul_def (g : Pose) (z : ℂ) : g • z = rot g.θ * z + g.p := rfl

/-- The `x`-coordinate of `g • z`: `cos θ · x - sin θ · y + pₓ`. -/
lemma smul_re (g : Pose) (z : ℂ) : (g • z).re = g.θ.cos * z.re - g.θ.sin * z.im + g.p.re := by
  simp [smul_def, rot_re, rot_im]
/-- The `y`-coordinate of `g • z`: `sin θ · x + cos θ · y + p_y`. -/
lemma smul_im (g : Pose) (z : ℂ) : (g • z).im = g.θ.sin * z.re + g.θ.cos * z.im + g.p.im := by
  simp [smul_def, rot_re, rot_im]; ring

/-- **Rigid motions preserve distances.** -/
theorem dist_smul (g : Pose) (z w : ℂ) : dist (g • z) (g • w) = dist z w := by
  simp [smul_def, dist_eq_norm, ← mul_sub]

/-- The action of each pose is an isometry of the plane. -/
theorem isometry_smul (g : Pose) : Isometry (g • · : ℂ → ℂ) :=
  Isometry.of_dist_eq (dist_smul g)
end Pose

/-! ## 2. `SE(2)` inside `E(2)`

We copy the definitions of the formal-conjectures moving-sofa file verbatim:
`ℝ² = EuclideanSpace ℝ (Fin 2)`, `E(2) = ℝ² ≃ᵃⁱ[ℝ] ℝ²`, topologised by inducing along
`toAffineIsometry.toContinuousAffineMap` (into the normed space of continuous affine maps). -/

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
/-- The Euclidean group of the plane: all affine isometric self-equivalences. -/
local notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The topology on `E(2)` used in `FormalConjectures/Wikipedia/MovingSofa.lean`. -/
noncomputable scoped instance instTopologicalSpaceE2 : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

scoped instance factFinrankPlane : Fact (Module.finrank ℝ ℝ² = 2) := ⟨finrank_euclideanSpace_fin⟩

/-- The determinant of the linear part of a planar Euclidean motion, as a monoid hom. -/
noncomputable def linDet : E(2) →* ℝ where
  toFun g := LinearMap.det (g.linearIsometryEquiv.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²)
  map_one' := LinearMap.det_id
  map_mul' a b := by
    rw [← LinearMap.det_comp]; rfl

theorem linDet_apply (g : E(2)) : linDet g = LinearMap.det (g.linearIsometryEquiv.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) := rfl

/-- The linear part of an isometry has determinant `±1`. -/
theorem linDet_eq_one_or (g : E(2)) : linDet g = 1 ∨ linDet g = -1 := by
  have h := (g.linearIsometryEquiv.toLinearIsometry).normDet_eq_one
  rw [LinearMap.normDet_eq_abs_det] at h
  exact abs_eq (zero_le_one) |>.mp h

/-- `SE(2)`: the orientation-preserving planar rigid motions (linear part of determinant 1). -/
def SE2 : Subgroup E(2) where
  carrier := {g | linDet g = 1}
  one_mem' := map_one linDet
  mul_mem' {a b} ha hb := by simp_all
  inv_mem' {a} ha := by
    have h : linDet a⁻¹ * linDet a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    change linDet a = 1 at ha
    change linDet a⁻¹ = 1
    rw [ha, mul_one] at h; exact h

/-- The standard orientation of `ℝ²`. -/
noncomputable def stdOr : Orientation ℝ ℝ² (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- Rotation by `θ` (about the origin) followed by translation by `v`. -/
noncomputable def rotTrans (θ : Real.Angle) (v : ℝ²) : E(2) :=
  (stdOr.rotation θ).toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ ℝ² v)

@[simp] theorem rotTrans_apply (θ : Real.Angle) (v x : ℝ²) : rotTrans θ v x = stdOr.rotation θ x + v := by
  simp [rotTrans]; abel

/-- Rotation-translations are orientation preserving. -/
theorem rotTrans_mem (θ : Real.Angle) (v : ℝ²) : rotTrans θ v ∈ SE2 := by
  have h : (rotTrans θ v).linearIsometryEquiv = stdOr.rotation θ := by
    ext x : 1; rfl
  show linDet _ = 1
  rw [linDet_apply, h]
  exact stdOr.det_rotation θ

/-- `SE(2)` is exactly the set of rotation-translations `x ↦ R(θ) x + v`. -/
theorem mem_SE2_iff (g : E(2)) : g ∈ SE2 ↔ ∃ θ v, g = rotTrans θ v := by
  constructor
  · intro hg
    obtain ⟨θ, hθ⟩ := stdOr.exists_linearIsometryEquiv_eq_of_det_pos
      (f := g.linearIsometryEquiv) (by rw [← linDet_apply]; rw [show linDet g = 1 from hg]; norm_num)
    refine ⟨θ, g 0, ?_⟩
    ext1 x
    rw [rotTrans_apply, ← hθ]
    have := g.map_vadd 0 x
    simpa using this
  · rintro ⟨θ, v, rfl⟩; exact rotTrans_mem θ v

/-- `g ↦ det(linear part of g)` is continuous for the moving-sofa topology on `E(2)`. -/
theorem continuous_linDet : Continuous linDet := by
  have h1 : Continuous (fun g : E(2) => g.toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom
  have h2 : Continuous (fun f : ℝ² →ᴬ[ℝ] ℝ² => f.contLinear) :=
    continuous_snd.comp (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²).continuous
  exact ContinuousLinearMap.continuous_det.comp (h2.comp h1)

/-- `SE(2)` is clopen in `E(2)` (the determinant only takes the values `±1`). -/
theorem isClopen_SE2 : IsClopen (SE2 : Set E(2)) := by
  constructor
  · exact isClosed_eq continuous_linDet continuous_const
  · have : (SE2 : Set E(2)) = linDet ⁻¹' Set.Ioi 0 := by
      ext g
      rcases linDet_eq_one_or g with h | h
      · simp [SE2, h]
      · simp [SE2, h]; norm_num
    rw [this]; exact isOpen_Ioi.preimage continuous_linDet

/-- A continuous family of motions over a preconnected space that is orientation preserving at
one point is orientation preserving everywhere. -/
theorem mem_SE2_of_continuous {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {m : X → E(2)} (hm : Continuous m) {x₀ : X} (h₀ : m x₀ ∈ SE2) (x : X) : m x ∈ SE2 := by
  have := (isClopen_SE2.preimage hm).eq_univ ⟨x₀, h₀⟩
  exact (Set.eq_univ_iff_forall.mp this x : _)

/-- **The moving-sofa `SE(2)` justification.** A continuous path `m : I → E(2)` with
`m 0 = id` stays in `SE(2)`. -/
theorem path_mem_SE2 {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) :
    m t ∈ SE2 :=
  mem_SE2_of_continuous hm (x₀ := 0) (by rw [h0]; exact SE2.one_mem) t

/-- Consequently every motion along such a path is a rotation followed by a translation. -/
theorem path_eq_rotTrans {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) :
    ∃ θ v, m t = rotTrans θ v := (mem_SE2_iff _).mp (path_mem_SE2 hm h0 t)

/-- The reflection across the line `ℝ e₀`, as an element of `E(2)`. -/
noncomputable def reflE2 : E(2) :=
  (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1:ℝ)).reflection.toAffineIsometryEquiv

theorem linDet_reflE2 : linDet reflE2 = -1 := by
  have := Submodule.det_reflection (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1:ℝ))
  have h1 : Fact (Module.finrank ℝ ℝ² = 1 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hr : Module.finrank ℝ (ℝ ∙ EuclideanSpace.single (0 : Fin 2) (1:ℝ))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton (n := 1) (by simp)
  rw [linDet_apply]
  exact this.trans (by rw [hr]; norm_num)

/-- A reflection is not in `SE(2)`; in particular `SE2 ≠ ⊤`, so the hypothesis `m 0 = id` in
`path_mem_SE2` cannot be dropped (the constant path at `reflE2` is continuous). -/
theorem reflE2_not_mem_SE2 : reflE2 ∉ SE2 := by
  intro h
  have : linDet reflE2 = 1 := h
  rw [linDet_reflE2] at this; norm_num at this

theorem SE2_ne_top : SE2 ≠ ⊤ := fun h => reflE2_not_mem_SE2 (h ▸ Subgroup.mem_top _)

open Real

/-! ## 3. Unicycle kinematics

`ẋ = v cos θ`, `ẏ = v sin θ`, `θ̇ = ω` with constant `v`, `ω`. -/

/-- A trajectory `(x, y, θ)` solves the unicycle ODE with constant inputs `v`, `ω`. -/
def IsUnicycleTraj (v ω : ℝ) (x y θ : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt x (v * Real.cos (θ t)) t ∧ HasDerivAt y (v * Real.sin (θ t)) t ∧
    HasDerivAt θ ω t

namespace Unicycle
variable (x₀ y₀ θ₀ v ω : ℝ)

/-- Heading `θ(t) = θ₀ + ω t`. -/
noncomputable def heading (t : ℝ) : ℝ := θ₀ + ω * t
/-- Arc solution, `x(t) = x₀ + (v/ω)(sin(θ₀+ωt) - sin θ₀)`. -/
noncomputable def arcX (t : ℝ) : ℝ := x₀ + v / ω * (sin (θ₀ + ω * t) - sin θ₀)
/-- Arc solution, `y(t) = y₀ - (v/ω)(cos(θ₀+ωt) - cos θ₀)`. -/
noncomputable def arcY (t : ℝ) : ℝ := y₀ - v / ω * (cos (θ₀ + ω * t) - cos θ₀)
/-- Straight-line solution (`ω = 0`), `x(t) = x₀ + v t cos θ₀`. -/
noncomputable def lineX (t : ℝ) : ℝ := x₀ + v * t * cos θ₀
/-- Straight-line solution (`ω = 0`), `y(t) = y₀ + v t sin θ₀`. -/
noncomputable def lineY (t : ℝ) : ℝ := y₀ + v * t * sin θ₀

theorem hasDerivAt_heading (t : ℝ) : HasDerivAt (heading θ₀ ω) ω t := by
  exact (((hasDerivAt_id t).const_mul ω).const_add θ₀).congr_deriv (by ring)

variable {x₀ y₀ θ₀ v ω}

theorem hasDerivAt_arcX (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (arcX x₀ θ₀ v ω) (v * cos (heading θ₀ ω t)) t := by
  have h := (((hasDerivAt_heading θ₀ ω t).sin).sub_const (sin θ₀)).const_mul (v / ω) |>.const_add x₀
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_arcY (hω : ω ≠ 0) (t : ℝ) :
    HasDerivAt (arcY y₀ θ₀ v ω) (v * sin (heading θ₀ ω t)) t := by
  have h := (((hasDerivAt_heading θ₀ ω t).cos).sub_const (cos θ₀)).const_mul (v / ω) |>.const_sub y₀
  refine h.congr_deriv ?_
  field_simp

theorem arc_initial : arcX x₀ θ₀ v ω 0 = x₀ ∧ arcY y₀ θ₀ v ω 0 = y₀ ∧ heading θ₀ ω 0 = θ₀ := by
  simp [arcX, arcY, heading]

/-- The arc solution lies on the circle of radius `|v/ω|` about
`(x₀ - (v/ω) sin θ₀, y₀ + (v/ω) cos θ₀)`. -/
theorem arc_on_circle (t : ℝ) :
    (arcX x₀ θ₀ v ω t - (x₀ - v / ω * sin θ₀)) ^ 2 + (arcY y₀ θ₀ v ω t - (y₀ + v / ω * cos θ₀)) ^ 2
      = (v / ω) ^ 2 := by
  have := sin_sq_add_cos_sq (θ₀ + ω * t)
  simp only [arcX, arcY]
  linear_combination (v / ω) ^ 2 * this

/-- Distance from the centre of turning is constantly `|v/ω|`. -/
theorem arc_dist_center (t : ℝ) :
    √((arcX x₀ θ₀ v ω t - (x₀ - v / ω * sin θ₀)) ^ 2 + (arcY y₀ θ₀ v ω t - (y₀ + v / ω * cos θ₀)) ^ 2)
      = |v / ω| := by
  rw [arc_on_circle, sqrt_sq_eq_abs]

theorem hasDerivAt_lineX (t : ℝ) : HasDerivAt (lineX x₀ θ₀ v) (v * cos θ₀) t := by
  exact ((((hasDerivAt_id t).const_mul v).mul_const (cos θ₀)).const_add x₀).congr_deriv (by ring)

theorem hasDerivAt_lineY (t : ℝ) : HasDerivAt (lineY y₀ θ₀ v) (v * sin θ₀) t := by
  exact ((((hasDerivAt_id t).const_mul v).mul_const (sin θ₀)).const_add y₀).congr_deriv (by ring)

theorem heading_zero (t : ℝ) : heading θ₀ 0 t = θ₀ := by simp [heading]
/-- **Arc solution** of the unicycle ODE for `ω ≠ 0`. -/
theorem isUnicycleTraj_arc (hω : ω ≠ 0) :
    IsUnicycleTraj v ω (arcX x₀ θ₀ v ω) (arcY y₀ θ₀ v ω) (heading θ₀ ω) :=
  fun t => ⟨hasDerivAt_arcX hω t, hasDerivAt_arcY hω t, hasDerivAt_heading θ₀ ω t⟩

/-- **Straight-line solution** of the unicycle ODE for `ω = 0`. -/
theorem isUnicycleTraj_line :
    IsUnicycleTraj v 0 (lineX x₀ θ₀ v) (lineY y₀ θ₀ v) (heading θ₀ 0) := fun t => by
  simp only [heading_zero]
  exact ⟨hasDerivAt_lineX t, hasDerivAt_lineY t, hasDerivAt_heading θ₀ 0 t⟩
end Unicycle

/-! ## 4–5. Two-link planar arm: workspace and singularities -/

namespace TwoLink
variable (l₁ l₂ : ℝ)

/-- Forward kinematics, `x = l₁ cos q₁ + l₂ cos(q₁+q₂)`. -/
noncomputable def fkX (q₁ q₂ : ℝ) : ℝ := l₁ * cos q₁ + l₂ * cos (q₁ + q₂)
/-- Forward kinematics, `y = l₁ sin q₁ + l₂ sin(q₁+q₂)`. -/
noncomputable def fkY (q₁ q₂ : ℝ) : ℝ := l₁ * sin q₁ + l₂ * sin (q₁ + q₂)
/-- Forward kinematics as a point of `ℂ`: `l₁ e^{iq₁} + l₂ e^{i(q₁+q₂)}`. -/
noncomputable def fk (q₁ q₂ : ℝ) : ℂ :=
  l₁ * Complex.exp (q₁ * Complex.I) + l₂ * Complex.exp ((q₁ + q₂ : ℝ) * Complex.I)

@[simp] theorem fk_re (q₁ q₂ : ℝ) : (fk l₁ l₂ q₁ q₂).re = fkX l₁ l₂ q₁ q₂ := by
  simp only [fk, fkX, Complex.add_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
@[simp] theorem fk_im (q₁ q₂ : ℝ) : (fk l₁ l₂ q₁ q₂).im = fkY l₁ l₂ q₁ q₂ := by
  simp only [fk, fkY, Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- Law of cosines for the arm: `x² + y² = l₁² + l₂² + 2 l₁ l₂ cos q₂`. -/
theorem fkX_sq_add_fkY_sq (q₁ q₂ : ℝ) :
    fkX l₁ l₂ q₁ q₂ ^ 2 + fkY l₁ l₂ q₁ q₂ ^ 2 = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos q₂ := by
  simp only [fkX, fkY, cos_add, sin_add]
  have h1 := sin_sq_add_cos_sq q₁
  have h2 := sin_sq_add_cos_sq q₂
  linear_combination (l₁ ^ 2 + 2 * l₁ * l₂ * cos q₂ + l₂ ^ 2 * (cos q₂ ^ 2 + sin q₂ ^ 2)) * h1
    + l₂ ^ 2 * h2

theorem norm_fk_sq (q₁ q₂ : ℝ) :
    ‖fk l₁ l₂ q₁ q₂‖ ^ 2 = l₁ ^ 2 + l₂ ^ 2 + 2 * l₁ * l₂ * cos q₂ := by
  rw [Complex.sq_norm, Complex.normSq_apply, fk_re, fk_im, ← fkX_sq_add_fkY_sq]; ring

theorem fk_eq_rot (q₁ q₂ : ℝ) :
    fk l₁ l₂ q₁ q₂ = Complex.exp (q₁ * Complex.I) * fk l₁ l₂ 0 q₂ := by
  simp only [fk, Complex.ofReal_zero, zero_mul, Complex.exp_zero, zero_add, Complex.ofReal_add]
  rw [add_mul, Complex.exp_add]; ring

variable {l₁ l₂}

/-- Outer workspace bound `‖p‖ ≤ l₁ + l₂`. -/
theorem norm_fk_le (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (q₁ q₂ : ℝ) : ‖fk l₁ l₂ q₁ q₂‖ ≤ l₁ + l₂ := by
  have h := norm_fk_sq l₁ l₂ q₁ q₂
  have hc := cos_le_one q₂
  have : ‖fk l₁ l₂ q₁ q₂‖ ^ 2 ≤ (l₁ + l₂) ^ 2 := by
    rw [h]; nlinarith [mul_nonneg h₁ h₂]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this

/-- Inner workspace bound `|l₁ - l₂| ≤ ‖p‖`. -/
theorem abs_sub_le_norm_fk (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (q₁ q₂ : ℝ) :
    |l₁ - l₂| ≤ ‖fk l₁ l₂ q₁ q₂‖ := by
  have h := norm_fk_sq l₁ l₂ q₁ q₂
  have hc := neg_one_le_cos q₂
  have : |l₁ - l₂| ^ 2 ≤ ‖fk l₁ l₂ q₁ q₂‖ ^ 2 := by
    rw [h, sq_abs]; nlinarith [mul_nonneg h₁ h₂]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- **Inverse kinematics existence**: every point of the closed annulus is reachable
(`q₂ = arccos c` by the law of cosines, `q₁` from the argument). -/
theorem exists_fk_eq (h₁ : 0 < l₁) (h₂ : 0 < l₂) {z : ℂ}
    (hlo : |l₁ - l₂| ≤ ‖z‖) (hhi : ‖z‖ ≤ l₁ + l₂) : ∃ q₁ q₂, fk l₁ l₂ q₁ q₂ = z := by
  set c := (‖z‖ ^ 2 - l₁ ^ 2 - l₂ ^ 2) / (2 * l₁ * l₂) with hc
  have hpos : 0 < 2 * l₁ * l₂ := by positivity
  have hlo2 : (l₁ - l₂) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hlo 2
  have hhi2 : ‖z‖ ^ 2 ≤ (l₁ + l₂) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hhi 2
  have hc1 : -1 ≤ c := by rw [hc, le_div_iff₀ hpos]; nlinarith
  have hc2 : c ≤ 1 := by rw [hc, div_le_iff₀ hpos]; nlinarith
  set q₂ := arccos c
  have hcos : cos q₂ = c := cos_arccos hc1 hc2
  have hw : ‖fk l₁ l₂ 0 q₂‖ = ‖z‖ := by
    have h := norm_fk_sq l₁ l₂ 0 q₂
    rw [hcos, hc] at h
    field_simp at h
    have : ‖fk l₁ l₂ 0 q₂‖ ^ 2 = ‖z‖ ^ 2 := by linear_combination h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  by_cases hw0 : fk l₁ l₂ 0 q₂ = 0
  · refine ⟨0, q₂, ?_⟩
    rw [hw0, norm_zero] at hw
    rw [hw0, (norm_eq_zero.mp hw.symm)]
  · have : ‖z / fk l₁ l₂ 0 q₂‖ = 1 := by
      rw [norm_div, hw, div_self]; rw [← hw]; exact norm_ne_zero_iff.mpr hw0
    obtain ⟨q₁, hq₁⟩ := (Complex.norm_eq_one_iff _).mp this
    refine ⟨q₁, q₂, ?_⟩
    rw [fk_eq_rot, hq₁, div_mul_cancel₀ _ hw0]

/-- **The workspace of the two-link arm is the closed annulus**
`|l₁ - l₂| ≤ ‖p‖ ≤ l₁ + l₂`. -/
theorem range_fk (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    Set.range (fun q : ℝ × ℝ => fk l₁ l₂ q.1 q.2) = {z | |l₁ - l₂| ≤ ‖z‖ ∧ ‖z‖ ≤ l₁ + l₂} := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨abs_sub_le_norm_fk h₁.le h₂.le _ _, norm_fk_le h₁.le h₂.le _ _⟩
  · rintro ⟨hlo, hhi⟩
    obtain ⟨q₁, q₂, h⟩ := exists_fk_eq h₁ h₂ hlo hhi
    exact ⟨(q₁, q₂), h⟩

variable (l₁ l₂)

/-- The Jacobian `∂(x,y)/∂(q₁,q₂)` (entries justified by the `hasDerivAt_fk*` lemmas). -/
noncomputable def jacobian (q₁ q₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-l₁ * sin q₁ - l₂ * sin (q₁ + q₂), -l₂ * sin (q₁ + q₂);
     l₁ * cos q₁ + l₂ * cos (q₁ + q₂), l₂ * cos (q₁ + q₂)]

theorem hasDerivAt_fkX_q₁ (q₁ q₂ : ℝ) :
    HasDerivAt (fun q => fkX l₁ l₂ q q₂) (jacobian l₁ l₂ q₁ q₂ 0 0) q₁ := by
  have h := ((hasDerivAt_cos q₁).const_mul l₁).add
    ((((hasDerivAt_id q₁).add_const q₂).cos).const_mul l₂)
  exact h.congr_deriv (by simp [jacobian]; ring)

theorem hasDerivAt_fkX_q₂ (q₁ q₂ : ℝ) :
    HasDerivAt (fun q => fkX l₁ l₂ q₁ q) (jacobian l₁ l₂ q₁ q₂ 0 1) q₂ := by
  have h := ((((hasDerivAt_id q₂).const_add q₁).cos).const_mul l₂).const_add (l₁ * cos q₁)
  exact h.congr_deriv (by simp [jacobian])

theorem hasDerivAt_fkY_q₁ (q₁ q₂ : ℝ) :
    HasDerivAt (fun q => fkY l₁ l₂ q q₂) (jacobian l₁ l₂ q₁ q₂ 1 0) q₁ := by
  have h := ((hasDerivAt_sin q₁).const_mul l₁).add
    ((((hasDerivAt_id q₁).add_const q₂).sin).const_mul l₂)
  exact h.congr_deriv (by simp [jacobian])

theorem hasDerivAt_fkY_q₂ (q₁ q₂ : ℝ) :
    HasDerivAt (fun q => fkY l₁ l₂ q₁ q) (jacobian l₁ l₂ q₁ q₂ 1 1) q₂ := by
  have h := ((((hasDerivAt_id q₂).const_add q₁).sin).const_mul l₂).const_add (l₁ * sin q₁)
  exact h.congr_deriv (by simp [jacobian])

/-- `det J = l₁ l₂ sin q₂`. -/
theorem det_jacobian (q₁ q₂ : ℝ) : (jacobian l₁ l₂ q₁ q₂).det = l₁ * l₂ * sin q₂ := by
  rw [jacobian, Matrix.det_fin_two_of]
  rw [show sin q₂ = sin ((q₁ + q₂) - q₁) by ring_nf, sin_sub]
  ring

variable {l₁ l₂}

/-- Singular configurations: `q₂ ≡ 0` or `q₂ ≡ π` (mod `2π`). -/
theorem det_jacobian_eq_zero_iff (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0) (q₁ q₂ : ℝ) :
    (jacobian l₁ l₂ q₁ q₂).det = 0 ↔ (q₂ : Real.Angle) = 0 ∨ (q₂ : Real.Angle) = π := by
  rw [det_jacobian, ← Real.Angle.sin_eq_zero_iff, Real.Angle.sin_coe]
  simp [h₁, h₂]

/-- Singular configurations: `q₂ = kπ`. -/
theorem det_jacobian_eq_zero_iff' (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0) (q₁ q₂ : ℝ) :
    (jacobian l₁ l₂ q₁ q₂).det = 0 ↔ ∃ k : ℤ, (k : ℝ) * π = q₂ := by
  rw [det_jacobian, ← sin_eq_zero_iff]
  simp [h₁, h₂]

/-- Singular configurations are exactly those whose end effector is on the boundary of the
workspace annulus. -/
theorem det_jacobian_eq_zero_iff_boundary (h₁ : 0 < l₁) (h₂ : 0 < l₂) (q₁ q₂ : ℝ) :
    (jacobian l₁ l₂ q₁ q₂).det = 0 ↔
      ‖fk l₁ l₂ q₁ q₂‖ = l₁ + l₂ ∨ ‖fk l₁ l₂ q₁ q₂‖ = |l₁ - l₂| := by
  have hpos : 0 < l₁ * l₂ := mul_pos h₁ h₂
  have hsq := norm_fk_sq l₁ l₂ q₁ q₂
  have e1 : ‖fk l₁ l₂ q₁ q₂‖ = l₁ + l₂ ↔ cos q₂ = 1 := by
    rw [← pow_left_inj₀ (norm_nonneg _) (by positivity : (0:ℝ) ≤ l₁ + l₂) two_ne_zero, hsq]
    constructor
    · intro h; have : l₁ * l₂ * (cos q₂ - 1) = 0 := by linear_combination h / 2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpos.ne'
      · linarith
    · intro h; rw [h]; ring
  have e2 : ‖fk l₁ l₂ q₁ q₂‖ = |l₁ - l₂| ↔ cos q₂ = -1 := by
    rw [← pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero, hsq, sq_abs]
    constructor
    · intro h; have : l₁ * l₂ * (cos q₂ + 1) = 0 := by linear_combination h / 2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hpos.ne'
      · linarith
    · intro h; rw [h]; ring
  rw [e1, e2, det_jacobian, ← sin_eq_zero_iff_cos_eq]
  simp [h₁.ne', h₂.ne']
end TwoLink

/-! ## 6. Differential drive -/

namespace DiffDrive

/-- Body twist `(v, ω)` from wheel (rim) speeds `(v_L, v_R)` with track width `b`:
`v = (v_R + v_L)/2`, `ω = (v_R - v_L)/b`. -/
noncomputable def toTwist (b : ℝ) (w : ℝ × ℝ) : ℝ × ℝ := ((w.2 + w.1) / 2, (w.2 - w.1) / b)

/-- Wheel speeds from body twist: `v_L = v - bω/2`, `v_R = v + bω/2`. -/
noncomputable def toWheels (b : ℝ) (t : ℝ × ℝ) : ℝ × ℝ := (t.1 - b * t.2 / 2, t.1 + b * t.2 / 2)

theorem toTwist_toWheels {b : ℝ} (hb : b ≠ 0) (t : ℝ × ℝ) : toTwist b (toWheels b t) = t := by
  ext
  · simp only [toTwist, toWheels]; ring
  · simp only [toTwist, toWheels]; field_simp; ring

theorem toWheels_toTwist {b : ℝ} (hb : b ≠ 0) (w : ℝ × ℝ) : toWheels b (toTwist b w) = w := by
  ext <;> simp [toTwist, toWheels] <;> field_simp <;> ring

/-- For track width `b > 0` the wheel-speed ↔ twist map is a linear equivalence. -/
noncomputable def equiv {b : ℝ} (hb : 0 < b) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := toTwist b
  invFun := toWheels b
  left_inv := toWheels_toTwist hb.ne'
  right_inv := toTwist_toWheels hb.ne'
  map_add' x y := by ext <;> simp [toTwist] <;> ring
  map_smul' c x := by ext <;> simp [toTwist] <;> ring

end DiffDrive

end RoboLean.Kinematics
