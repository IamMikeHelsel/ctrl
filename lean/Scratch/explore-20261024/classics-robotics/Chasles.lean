import RoboLean.Kinematics
import ControlsLean.Vision.Epipolar

/-!
# Chasles' theorem (1830)

* Planar: every proper rigid motion of the plane that is not a translation is a rotation about a
  unique fixed point (the instantaneous/finite centre of rotation).
* Spatial: for a Rodrigues rotation `R = I + s K + (1-c) K²` (with `K³ = -K`, `c ≠ 1`) and any
  translation `t`, the motion `x ↦ R x + t` is a screw: rotation about the axis through `p`
  plus translation `h a` along the axis, with the classical
  `p = ½ (t⊥ + cot(θ/2) · a × t)`.
-/

namespace Classics.Chasles

open RoboLean.Kinematics Pose

lemma rot_eq_one_iff (θ : Real.Angle) : rot θ = 1 ↔ θ = 0 := by
  constructor
  · intro h
    have : θ.toCircle = 1 := Circle.ext (by simpa [rot] using h)
    have h2 := Real.Angle.arg_toCircle θ
    rw [this] at h2
    simpa using h2.symm
  · rintro rfl; simp

/-- **Planar Chasles.** A non-translational pose `g` (heading `θ ≠ 0`) has a unique fixed point
`c`, and acts as the rotation by `θ` about `c`. -/
theorem planar_chasles (g : Pose) (hθ : g.θ ≠ 0) :
    ∃! c : ℂ, g • c = c ∧ ∀ z, g • z = rot g.θ * (z - c) + c := by
  have h1 : (1 : ℂ) - rot g.θ ≠ 0 := sub_ne_zero.2 (Ne.symm ((rot_eq_one_iff _).not.2 hθ))
  refine ⟨g.p / (1 - rot g.θ), ⟨?_, fun z => ?_⟩, ?_⟩
  · rw [smul_def]; field_simp; ring
  · rw [smul_def]; field_simp; ring
  · rintro c ⟨hc, -⟩
    rw [smul_def] at hc
    field_simp
    linear_combination -hc

/-- Pure translations (`θ = 0`, `p ≠ 0`) have no fixed point. -/
theorem translation_no_fixed (g : Pose) (hθ : g.θ = 0) (hp : g.p ≠ 0) (c : ℂ) : g • c ≠ c := by
  rw [smul_def, hθ, rot_zero, one_mul]; intro h; exact hp (by linear_combination h)

/-! ## Spatial Chasles, abstractly -/

section Abstract
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Rodrigues operator `R = 1 + s K + (1-c) K²`. -/
def rodrigues (K : Module.End ℝ E) (s c : ℝ) : Module.End ℝ E := 1 + s • K + (1 - c) • K ^ 2

/-- **Screw decomposition.** If `K³ = -K`, `s² + c² = 1`, `c ≠ 1`, then with
`p = ½(-K²t + (s/(1-c)) K t)` and axial part `τ = t + K² t` (which satisfies `K τ = 0`,
i.e. lies on the axis and is fixed by `R`):
`R x + t = R (x - p) + p + τ`. -/
theorem screw_decomp (K : Module.End ℝ E) (hK : K ^ 3 = -K) {s c : ℝ} (hsc : s ^ 2 + c ^ 2 = 1)
    (hc : c ≠ 1) (t x : E) :
    let p : E := (1 / 2 : ℝ) • (-(K ^ 2) t + (s / (1 - c)) • K t)
    rodrigues K s c x + t = rodrigues K s c (x - p) + p + (t + (K ^ 2) t) ∧
      K (t + (K ^ 2) t) = 0 := by
  intro p
  have hK3 : ∀ v, K (K (K v)) = -K v := fun v => by
    have := congrArg (fun f : Module.End ℝ E => f v) hK
    simpa [pow_succ, Module.End.mul_apply] using this
  have h1c : (1 - c) ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  refine ⟨?_, ?_⟩
  · -- reduce to `(1 - R) p = -K² t`
    have key : p - rodrigues K s c p = -(K ^ 2) t := by
      simp only [p, rodrigues, sq, Module.End.mul_apply, map_smul, map_add, map_neg, hK3,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, smul_add, smul_neg,
        smul_smul]
      have hk : s / (1 - c) * (1 - c) = s := by field_simp
      have hk2 : s / (1 - c) * s = 1 + c := by
        field_simp; linear_combination hsc
      linear_combination (norm := module) hk • ((1 / 2 : ℝ) • K t) - hk2 • ((1 / 2 : ℝ) • K (K t))
    have hlin : rodrigues K s c (x - p) = rodrigues K s c x - rodrigues K s c p := map_sub _ _ _
    rw [hlin]
    have : t = p - rodrigues K s c p + (t + (K ^ 2) t) := by rw [key]; abel
    conv_lhs => rw [this]
    abel
  · simp only [map_add, sq, Module.End.mul_apply, hK3]; abel

end Abstract

/-! ## Specialisation to `ℝ³` with `K = [a]×`, `‖a‖ = 1` -/

open Matrix ControlsLean.Vision

theorem skew_cube' (a : Fin 3 → ℝ) : skew a ^ 3 = -(a ⬝ᵥ a) • skew a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, dotProduct] <;> ring

theorem skew_cube (a : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) : skew a ^ 3 = -skew a := by
  rw [skew_cube', ha, neg_smul, one_smul]

theorem skew_sq_mulVec (a t : Fin 3 → ℝ) :
    (skew a * skew a) *ᵥ t = (a ⬝ᵥ t) • a - (a ⬝ᵥ a) • t := by
  ext i
  fin_cases i <;> simp [skew, Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_three] <;>
    ring

theorem axial_part (a t : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) :
    t + (skew a * skew a) *ᵥ t = (a ⬝ᵥ t) • a := by
  rw [skew_sq_mulVec, ha, one_smul]; abel

/-- **Chasles' screw theorem in `ℝ³`.** For the Rodrigues rotation about the unit axis `a` by
angle `θ` with `cos θ ≠ 1` and any translation `t`, there are a point `p` on the screw axis and a
pitch-translation `h = a ⬝ t` such that `R x + t = R (x - p) + p + h • a` for all `x`. -/
theorem chasles_R3 (a t : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) (θ : ℝ) (hθ : Real.cos θ ≠ 1) :
    let R := 1 + Real.sin θ • skew a + (1 - Real.cos θ) • (skew a * skew a)
    ∃ p : Fin 3 → ℝ, ∃ h : ℝ, ∀ x, R *ᵥ x + t = R *ᵥ (x - p) + p + h • a := by
  intro R
  let K : Module.End ℝ (Fin 3 → ℝ) := Matrix.toLin' (skew a)
  have hK : K ^ 3 = -K := by
    simp only [K, ← Matrix.toLin'_pow, skew_cube a ha, map_neg]
  have hRK : ∀ v, R *ᵥ v = rodrigues K (Real.sin θ) (Real.cos θ) v := fun v => by
    simp [R, rodrigues, K, sq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec]
  refine ⟨(1 / 2 : ℝ) • (-(K ^ 2) t + (Real.sin θ / (1 - Real.cos θ)) • K t), a ⬝ᵥ t,
    fun x => ?_⟩
  obtain ⟨h1, -⟩ := screw_decomp K hK (Real.sin_sq_add_cos_sq θ) hθ t x
  rw [hRK, hRK, h1, ← axial_part a t ha]
  simp [K, sq, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

end Classics.Chasles
