import RoboLean.Kinematics

/-!
# Bridge between `Pose` (complex model) and `SE2 ≤ E(2)`

* `φ : ℂ ≃ₗᵢ[ℝ] ℝ²`, `φ z = ![z.re, z.im]` (= `Complex.orthonormalBasisOneI.repr`).
* Orientation check: `map_stdOr` shows `φ.symm` carries `stdOr` (the orientation of the standard
  basis of `ℝ²`) to `Complex.orientation` (basis `1, I`). Hence (`φ_rotation`) `stdOr.rotation θ`
  is multiplication by `e^{iθ} = Pose.rot θ` under `φ`: no sign flip is needed.
* `poseEquivSE2 : Pose ≃* SE2` with `poseEquivSE2 ⟨θ, p⟩ = rotTrans θ (φ p)` and
  `poseEquivSE2_smul : poseEquivSE2 g (φ z) = φ (g • z)`.
* Paths: for continuous `m : I → E(2)` with `m 0 = id`, each `m t` is `toE2` of a unique pose
  (`path_existsUnique_pose`); the pose path `posePath` starts at `1` and has continuous position
  and continuous heading `e^{iθ(t)}`.
-/

namespace RoboLean.Kinematics

open scoped unitInterval

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The standard isometry `ℂ ≃ ℝ²`, `z ↦ (re z, im z)`. -/
noncomputable def φ : ℂ ≃ₗᵢ[ℝ] ℝ² := Complex.orthonormalBasisOneI.repr

@[simp] lemma φ_apply (z : ℂ) : φ z = ![z.re, z.im] := rfl
lemma φ_symm_apply (x : ℝ²) : φ.symm x = x 0 + x 1 * Complex.I := rfl

lemma map_stdOr : Orientation.map (Fin 2) φ.symm.toLinearEquiv stdOr = Complex.orientation := by
  rw [stdOr, ← Module.Basis.orientation_map, Complex.orientation]
  congr 1

/-- Under `φ`, rotation by `θ` for the standard orientation is multiplication by `e^{iθ}`. -/
theorem φ_symm_rotation (θ : Real.Angle) (x : ℝ²) :
    φ.symm (stdOr.rotation θ x) = Pose.rot θ * φ.symm x :=
  stdOr.rotation_map_complex θ φ.symm map_stdOr x


theorem φ_rotation (θ : Real.Angle) (z : ℂ) :
    stdOr.rotation θ (φ z) = φ (Pose.rot θ * z) := by
  apply φ.symm.injective
  rw [φ_symm_rotation]; simp

/-- A pose as a Euclidean motion: `rotTrans θ (φ p)`. -/
noncomputable def toE2 (g : Pose) : E(2) := rotTrans g.θ (φ g.p)

theorem toE2_apply (g : Pose) (x : ℝ²) : toE2 g x = φ (g • φ.symm x) := by
  apply φ.symm.injective
  rw [toE2, rotTrans_apply, map_add, φ_symm_rotation]; simp [Pose.smul_def]

/-- **Intertwining**: `toE2 g (φ z) = φ (g • z)`. -/
theorem toE2_apply_φ (g : Pose) (z : ℂ) : toE2 g (φ z) = φ (g • z) := by
  rw [toE2_apply, LinearIsometryEquiv.symm_apply_apply]

theorem toE2_mem (g : Pose) : toE2 g ∈ SE2 := rotTrans_mem _ _

/-- `Pose → SE2` as a monoid hom. -/
noncomputable def toSE2Hom : Pose →* SE2 where
  toFun g := ⟨toE2 g, toE2_mem g⟩
  map_one' := by
    ext x : 2
    simp [toE2_apply]
  map_mul' a b := by
    ext x : 2
    simp only [Subgroup.coe_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply, toE2_apply,
      LinearIsometryEquiv.symm_apply_apply, mul_smul]

lemma rot_injective : Function.Injective Pose.rot := by
  intro a b h
  rw [← Real.Angle.arg_toCircle a, ← Real.Angle.arg_toCircle b]
  exact congrArg (fun z : ℂ => (Complex.arg z : Real.Angle)) h

lemma toE2_injective : Function.Injective toE2 := by
  intro a b h
  have h0 := toE2_apply_φ a 0
  have h1 := toE2_apply_φ a 1
  rw [h, toE2_apply_φ] at h0 h1
  have hp : a.p = b.p := by simpa [Pose.smul_def] using (φ.injective h0).symm
  have hr : Pose.rot a.θ = Pose.rot b.θ := by
    simpa [Pose.smul_def, hp] using (φ.injective h1).symm
  exact Pose.ext (rot_injective hr) hp

/-- **The bridge**: planar poses are isomorphic to `SE(2) ≤ E(2)`. -/
noncomputable def poseEquivSE2 : Pose ≃* SE2 :=
  MulEquiv.ofBijective toSE2Hom ⟨fun a b h => toE2_injective (congrArg Subtype.val h), by
    rintro ⟨g, hg⟩
    obtain ⟨θ, v, rfl⟩ := (mem_SE2_iff g).mp hg
    exact ⟨⟨θ, φ.symm v⟩, by ext1; simp [toSE2Hom, toE2]⟩⟩

@[simp] theorem poseEquivSE2_apply_coe (g : Pose) :
    (poseEquivSE2 g : E(2)) = rotTrans g.θ (φ g.p) := rfl

theorem poseEquivSE2_mk (θ : Real.Angle) (p : ℂ) :
    (poseEquivSE2 ⟨θ, p⟩ : E(2)) = rotTrans θ (φ p) := rfl

/-- The isomorphism intertwines the actions on `ℂ` and on `ℝ²`. -/
theorem poseEquivSE2_smul (g : Pose) (z : ℂ) : (poseEquivSE2 g : E(2)) (φ z) = φ (g • z) :=
  toE2_apply_φ g z

/-- Every continuous path of motions from the identity is, at each time, a unique pose. -/
theorem path_existsUnique_pose {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²)
    (t : I) : ∃! g : Pose, toE2 g = m t := by
  obtain ⟨g, hg⟩ := poseEquivSE2.surjective ⟨m t, path_mem_SE2 hm h0 t⟩
  exact ⟨g, congrArg Subtype.val hg, fun g' hg' => toE2_injective (hg'.trans (congrArg Subtype.val hg).symm)⟩

/-- Evaluation `g ↦ g x` is continuous for the moving-sofa topology on `E(2)`. -/
theorem continuous_eval_E2 (x : ℝ²) : Continuous (fun g : E(2) => g x) := by
  have h1 : Continuous (fun g : E(2) => g.toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom
  let D := ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
  have h2 : Continuous (fun f : ℝ² →ᴬ[ℝ] ℝ² => f x) := by
    have : (fun f : ℝ² →ᴬ[ℝ] ℝ² => f x) = fun f => (D f).2 x + (D f).1 := by
      funext f
      conv_lhs => rw [← D.symm_apply_apply f]
      rfl
    rw [this]
    exact ((continuous_snd.comp D.continuous).clm_apply continuous_const).add
      (continuous_fst.comp D.continuous)
  exact h2.comp h1

/-- The pose at time `t` along a continuous path of motions starting at the identity. -/
noncomputable def posePath {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) :
    Pose :=
  poseEquivSE2.symm ⟨m t, path_mem_SE2 hm h0 t⟩

theorem toE2_posePath {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) :
    toE2 (posePath hm h0 t) = m t :=
  congrArg Subtype.val (poseEquivSE2.apply_symm_apply ⟨m t, path_mem_SE2 hm h0 t⟩)

theorem posePath_zero {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) :
    posePath hm h0 0 = 1 := by
  apply toE2_injective
  rw [toE2_posePath, h0]
  exact (congrArg Subtype.val (map_one toSE2Hom)).symm

theorem posePath_p {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) :
    (posePath hm h0 t).p = φ.symm (m t 0) := by
  rw [← toE2_posePath hm h0 t, ← map_zero φ, toE2_apply_φ]; simp [Pose.smul_def]

theorem rot_posePath {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) (t : I) :
    Pose.rot (posePath hm h0 t).θ = φ.symm (m t (φ 1)) - φ.symm (m t 0) := by
  rw [← posePath_p hm h0, ← toE2_posePath hm h0 t, toE2_apply_φ]; simp [Pose.smul_def]

/-- The position along the path is continuous. -/
theorem continuous_posePath_p {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) :
    Continuous fun t => (posePath hm h0 t).p := by
  simp_rw [posePath_p]
  exact φ.symm.continuous.comp ((continuous_eval_E2 0).comp hm)

/-- The heading `e^{iθ(t)}` along the path is continuous. -/
theorem continuous_rot_posePath {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) :
    Continuous fun t => Pose.rot (posePath hm h0 t).θ := by
  simp_rw [rot_posePath]
  exact (φ.symm.continuous.comp ((continuous_eval_E2 _).comp hm)).sub
    (φ.symm.continuous.comp ((continuous_eval_E2 0).comp hm))

end RoboLean.Kinematics
