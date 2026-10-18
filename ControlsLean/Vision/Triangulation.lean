/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Vision.Epipolar
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Two-view triangulation: unique depths and closed form

In the setting of `epipolar_constraint`, a scene point seen along ray `x₁` in camera 1 and ray
`x₂` in camera 2 satisfies `d₂ x₂ = R (d₁ x₁) + t` for depths `d₁, d₂`. If the rays `x₂` and
`R x₁` are not parallel (`n := x₂ × R x₁ ≠ 0`), the depths are unique and given by
`d₁ = −(n · (x₂ × t)) / (n · n)` and `d₂ = −(n · (R x₁ × t)) / (n · n)`,
obtained by crossing the scene equation with `x₂` and with `R x₁` respectively.

Conversely, for non-parallel rays a depth pair exists iff the epipolar constraint holds, and the
closed forms then solve the scene equation. Finally (cheirality), replacing `t` by `−t` negates
both depths, so a positive-depth solution fixes the sign of `t` left ambiguous by `E`.

Here `n · n` plays the role of `‖n‖²` (the Euclidean norm squared; the default norm on
`Fin 3 → ℝ` is the sup norm).
-/

open Matrix

namespace ControlsLean.Vision

section Field

variable {K : Type*} [Field K]

/-- Crossing the scene equation with `x₂` eliminates `d₂`. -/
theorem smul_cross_eq_of_scene {R : Matrix (Fin 3) (Fin 3) K} {t x₁ x₂ : Fin 3 → K} {d₁ d₂ : K}
    (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₁ • (x₂ ⨯₃ (R *ᵥ x₁)) = -(x₂ ⨯₃ t) := by
  have := congrArg (x₂ ⨯₃ ·) h
  simp only [mulVec_smul, map_add, map_smul, cross_self, smul_zero] at this
  exact eq_neg_of_add_eq_zero_left this.symm

/-- Crossing the scene equation with `R x₁` eliminates `d₁`. -/
theorem smul_cross_eq_of_scene' {R : Matrix (Fin 3) (Fin 3) K} {t x₁ x₂ : Fin 3 → K} {d₁ d₂ : K}
    (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₂ • (x₂ ⨯₃ (R *ᵥ x₁)) = -((R *ᵥ x₁) ⨯₃ t) := by
  have := congrArg ((R *ᵥ x₁) ⨯₃ ·) h
  simp only [mulVec_smul, map_add, map_smul, cross_self, smul_zero, zero_add] at this
  rw [← cross_anticomm, smul_neg, this]

/-- The polynomial identity behind existence: the residual of the scene equation at the
(cleared-denominator) closed-form depths is the epipolar residual times `x₂ × a`. -/
theorem scene_closedForm_aux (t a x₂ : Fin 3 → K) :
    (-((x₂ ⨯₃ a) ⬝ᵥ (x₂ ⨯₃ t))) • a + ((x₂ ⨯₃ a) ⬝ᵥ (x₂ ⨯₃ a)) • t -
        (-((x₂ ⨯₃ a) ⬝ᵥ (a ⨯₃ t))) • x₂ = -(x₂ ⬝ᵥ (t ⨯₃ a)) • (x₂ ⨯₃ a) := by
  ext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three] <;> ring

theorem essential_neg (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    essential R (-t) = -essential R t := by
  have : skew (-t) = -skew t := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew]
  rw [essential, essential, this, neg_mul]

end Field

variable {R : Matrix (Fin 3) (Fin 3) ℝ} {t x₁ x₂ : Fin 3 → ℝ} {d₁ d₂ : ℝ}

private theorem dotProduct_self_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 :=
  fun h => hv (dotProduct_self_eq_zero.mp h)

/-- **Triangulation, closed form for `d₁`.** -/
theorem depth₁_eq (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0) (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₁ = -((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ t)) /
      ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁))) := by
  rw [eq_div_iff (dotProduct_self_ne_zero hn)]
  have := congrArg ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ ·) (smul_cross_eq_of_scene h)
  rwa [dotProduct_smul, dotProduct_neg, smul_eq_mul] at this

/-- **Triangulation, closed form for `d₂`.** -/
theorem depth₂_eq (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0) (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) :
    d₂ = -((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ ((R *ᵥ x₁) ⨯₃ t)) /
      ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁))) := by
  rw [eq_div_iff (dotProduct_self_ne_zero hn)]
  have := congrArg ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ ·) (smul_cross_eq_of_scene' h)
  rwa [dotProduct_smul, dotProduct_neg, smul_eq_mul] at this

/-- **Triangulation is unique.** For non-parallel rays, at most one depth pair satisfies the
scene equation. -/
theorem depths_unique (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0) {e₁ e₂ : ℝ}
    (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) (h' : e₂ • x₂ = R *ᵥ (e₁ • x₁) + t) :
    d₁ = e₁ ∧ d₂ = e₂ :=
  ⟨(depth₁_eq hn h).trans (depth₁_eq hn h').symm, (depth₂_eq hn h).trans (depth₂_eq hn h').symm⟩

/-- **Existence.** For non-parallel rays satisfying the epipolar constraint, the closed-form
depths solve the scene equation. -/
theorem scene_closedForm (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0)
    (hE : x₂ ⬝ᵥ (essential R t *ᵥ x₁) = 0) :
    (-((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ ((R *ᵥ x₁) ⨯₃ t)) /
        ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)))) • x₂ =
      R *ᵥ ((-((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ t)) /
        ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)))) • x₁) + t := by
  have hq := dotProduct_self_ne_zero hn
  have key := scene_closedForm_aux t (R *ᵥ x₁) x₂
  rw [essential_mulVec] at hE
  rw [hE, neg_zero, zero_smul] at key
  have hc : ∀ p : ℝ, (x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)) *
      (p / ((x₂ ⨯₃ (R *ᵥ x₁)) ⬝ᵥ (x₂ ⨯₃ (R *ᵥ x₁)))) = p := fun p => by field_simp
  apply smul_right_injective _ hq
  simp only [mulVec_smul, smul_add, smul_smul, hc]
  linear_combination (norm := module) -key

/-- For non-parallel rays, a depth pair exists iff the epipolar constraint holds. -/
theorem exists_depths_iff (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0) :
    (∃ d₁ d₂ : ℝ, d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) ↔ x₂ ⬝ᵥ (essential R t *ᵥ x₁) = 0 := by
  refine ⟨fun ⟨d₁, d₂, h⟩ => ?_, fun hE => ⟨_, _, scene_closedForm hn hE⟩⟩
  have ht : t = d₂ • x₂ - d₁ • (R *ᵥ x₁) := by rw [h, mulVec_smul]; abel
  rw [essential_mulVec, ht]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, cross_self,
    smul_zero, sub_zero, dotProduct_smul, dot_self_cross, smul_eq_mul, mul_zero]

/-- Negating the translation negates both depths. -/
theorem scene_neg_iff :
    d₂ • x₂ = R *ᵥ (d₁ • x₁) + t ↔ (-d₂) • x₂ = R *ᵥ ((-d₁) • x₁) + -t := by
  simp only [neg_smul, mulVec_neg, ← neg_add, neg_inj]

/-- **Cheirality.** `E = [t]ₓ R` determines `t` only up to sign (`essential R (-t) = -E`). For
non-parallel rays, a solution with translation `-t` has the negated depths, so if the point has
positive depths for `t`, it has negative depths for `-t`. -/
theorem cheirality (hn : x₂ ⨯₃ (R *ᵥ x₁) ≠ 0) {e₁ e₂ : ℝ}
    (h : d₂ • x₂ = R *ᵥ (d₁ • x₁) + t) (h' : e₂ • x₂ = R *ᵥ (e₁ • x₁) + -t)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) : e₁ < 0 ∧ e₂ < 0 := by
  obtain ⟨h₁, h₂⟩ := depths_unique hn (scene_neg_iff.mp h) h'
  exact ⟨h₁ ▸ neg_neg_of_pos hd₁, h₂ ▸ neg_neg_of_pos hd₂⟩

end ControlsLean.Vision
