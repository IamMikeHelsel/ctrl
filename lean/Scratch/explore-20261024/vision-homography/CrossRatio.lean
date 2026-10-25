import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Matrix

namespace VisionExplore

variable {K : Type*} [Field K]

/-- 2×2 bracket of homogeneous points on `P¹`. -/
def br2 (p q : Fin 2 → K) : K := p 0 * q 1 - p 1 * q 0

/-- Homogeneous cross-ratio `[p₁p₃][p₂p₄] / ([p₁p₄][p₂p₃])`. -/
def cr (p₁ p₂ p₃ p₄ : Fin 2 → K) : K := br2 p₁ p₃ * br2 p₂ p₄ / (br2 p₁ p₄ * br2 p₂ p₃)

theorem br2_mulVec (H : Matrix (Fin 2) (Fin 2) K) (p q : Fin 2 → K) :
    br2 (H *ᵥ p) (H *ᵥ q) = H.det * br2 p q := by
  simp [br2, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]; ring

/-- **Cross-ratio invariance on `P¹`** (no distinctness hypotheses: degenerate cases give
`0 = 0` because Lean's `x / 0 = 0`). -/
theorem cr_mulVec (H : Matrix (Fin 2) (Fin 2) K) (hH : H.det ≠ 0) (p₁ p₂ p₃ p₄ : Fin 2 → K) :
    cr (H *ᵥ p₁) (H *ᵥ p₂) (H *ᵥ p₃) (H *ᵥ p₄) = cr p₁ p₂ p₃ p₄ := by
  simp only [cr, br2_mulVec]
  rw [mul_mul_mul_comm, mul_mul_mul_comm H.det (br2 p₁ p₄),
    mul_div_mul_left _ _ (mul_ne_zero hH hH)]

/-- Cross-ratio is invariant under rescaling each homogeneous representative (well-defined on
`P¹`), provided the scalars are nonzero. -/
theorem cr_smul (a b c d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (p₁ p₂ p₃ p₄ : Fin 2 → K) :
    cr (a • p₁) (b • p₂) (c • p₃) (d • p₄) = cr p₁ p₂ p₃ p₄ := by
  have e : ∀ (s t : K) (p q : Fin 2 → K), br2 (s • p) (t • q) = (s * t) * br2 p q := by
    intro s t p q; simp [br2]; ring
  simp only [cr, e]
  rw [show a * c * br2 p₁ p₃ * (b * d * br2 p₂ p₄) = (a * b * c * d) * (br2 p₁ p₃ * br2 p₂ p₄)
    by ring, show a * d * br2 p₁ p₄ * (b * c * br2 p₂ p₃) = (a * b * c * d) *
      (br2 p₁ p₄ * br2 p₂ p₃) by ring]
  exact mul_div_mul_left _ _ (by simp [ha, hb, hc, hd])

/-! ### Points on a line in `P²` -/

abbrev br3 (o p q : Fin 3 → K) : K := (Matrix.of ![o, p, q]).det

/-- Point `c 0 • u + c 1 • v` on the line spanned by `u, v`. -/
def linePt (u v : Fin 3 → K) (c : Fin 2 → K) : Fin 3 → K := c 0 • u + c 1 • v

/-- Joining with any external point `o`: `[o, L(c), L(c')] = [c c'] · [o u v]`. -/
theorem br3_linePt (o u v : Fin 3 → K) (c c' : Fin 2 → K) :
    br3 o (linePt u v c) (linePt u v c') = br2 c c' * br3 o u v := by
  simp [br3, linePt, br2, det_fin_three]; ring

/-- Cross-ratio of four points of `P²` seen from a viewpoint `o`. -/
def crFrom (o p₁ p₂ p₃ p₄ : Fin 3 → K) : K :=
  br3 o p₁ p₃ * br3 o p₂ p₄ / (br3 o p₁ p₄ * br3 o p₂ p₃)

/-- **Viewpoint independence.** For collinear points, the cross-ratio seen from any `o` off the
line equals the intrinsic `P¹` cross-ratio of their line coordinates. -/
theorem crFrom_linePt (o u v : Fin 3 → K) (ho : br3 o u v ≠ 0) (c₁ c₂ c₃ c₄ : Fin 2 → K) :
    crFrom o (linePt u v c₁) (linePt u v c₂) (linePt u v c₃) (linePt u v c₄) = cr c₁ c₂ c₃ c₄ := by
  simp only [crFrom, br3_linePt, cr]
  rw [mul_mul_mul_comm, mul_mul_mul_comm (br2 c₁ c₄), mul_div_mul_right _ _ (mul_ne_zero ho ho)]

/-- `H` maps the line point `L_{u,v}(c)` to the line point `L_{Hu,Hv}(c)`. -/
theorem mulVec_linePt (H : Matrix (Fin 3) (Fin 3) K) (u v : Fin 3 → K) (c : Fin 2 → K) :
    H *ᵥ linePt u v c = linePt (H *ᵥ u) (H *ᵥ v) c := by
  simp [linePt, mulVec_add, mulVec_smul]

/-- **Cross-ratio invariance under a planar homography**, measured from *arbitrary*
viewpoints `o` (before) and `o'` (after) off the respective lines. -/
theorem crFrom_homography (H : Matrix (Fin 3) (Fin 3) K) (u v o o' : Fin 3 → K)
    (ho : br3 o u v ≠ 0) (ho' : br3 o' (H *ᵥ u) (H *ᵥ v) ≠ 0) (c₁ c₂ c₃ c₄ : Fin 2 → K) :
    crFrom o' (H *ᵥ linePt u v c₁) (H *ᵥ linePt u v c₂) (H *ᵥ linePt u v c₃)
        (H *ᵥ linePt u v c₄) =
      crFrom o (linePt u v c₁) (linePt u v c₂) (linePt u v c₃) (linePt u v c₄) := by
  simp only [mulVec_linePt]
  rw [crFrom_linePt _ _ _ ho', crFrom_linePt _ _ _ ho]

/-- Harmonic conjugate sanity check: `(0, ∞; 1, -1)` has cross-ratio `-1`. -/
example : cr (K := ℚ) ![1, 0] ![0, 1] ![1, 1] ![-1, 1] = -1 := by
  simp [cr, br2]

end VisionExplore
