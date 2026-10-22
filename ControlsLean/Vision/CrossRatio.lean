/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ControlsLean.Vision.Homography

/-!
# The Cross-Ratio: the Fundamental Projective Invariant

The cross-ratio of four points on a projective line is the basic numerical invariant of
projective geometry (Hartley & Zisserman, *Multiple View Geometry*, Section 2.5). It underlies
camera calibration from vanishing points and metric measurement from a single perspective image.

For homogeneous points $p_i \in K^2$ on the projective line $\mathbb{P}^1(K)$ over any field $K$,
writing $[p\,q] = p_0 q_1 - p_1 q_0$ for the $2 \times 2$ bracket (determinant),
$$\mathrm{CR}(p_1, p_2; p_3, p_4) = \frac{[p_1 p_3][p_2 p_4]}{[p_1 p_4][p_2 p_3]}.$$
Division follows Mathlib's convention `x / 0 = 0`, so every identity below holds without
side conditions on the denominators.

### Main Results Proved:
1. `bracket2_mulVec`: $[H p\; H q] = \det(H)\,[p\,q]$ for any $2 \times 2$ matrix $H$.
2. `crossRatio_mulVec`: the cross-ratio is invariant under every invertible $H \in GL(2, K)$.
3. `crossRatio_smul`: the cross-ratio is invariant under rescaling each $p_i$ by a nonzero scalar,
   so it is a well-defined function of four points of $\mathbb{P}^1(K)$.
4. `crossRatio_swap_34`: swapping $p_3, p_4$ inverts the cross-ratio.
5. `crossRatioAffine_mobius`: for scalars $a, b, c, d$, the affine cross-ratio
   $\frac{(a-c)(b-d)}{(a-d)(b-c)}$ is invariant under every Möbius map
   $x \mapsto \frac{\alpha x + \beta}{\gamma x + \delta}$ with $\alpha\delta - \beta\gamma \ne 0$,
   provided $\gamma x + \delta \ne 0$ at the four points.
6. `crossRatioFrom_linePt`: for four collinear image points $p_i = s_i u + t_i v \in K^3$ on the
   line through $u, v$, the cross-ratio measured from any vantage point $o$ off that line
   (via $3 \times 3$ determinants $[o\,p_i\,p_j]$) equals the cross-ratio of the line
   coordinates $(s_i, t_i)$; in particular it does not depend on $o$.
7. `crossRatioFrom_homography`, `crossRatio_collinear_homography`: the cross-ratio of four
   collinear image points is preserved by every invertible $3 \times 3$ homography.
8. Corollaries:
   - `crossRatio_midpoint_infinity`, `crossRatio_harmonic_homography`: the endpoints of a
     segment, its midpoint and the point at infinity form a harmonic range (cross-ratio $-1$),
     and every homography preserves this, so in a perspective image the midpoint's image is
     the harmonic conjugate of the vanishing point.
   - `crossRatioAffine_equally_spaced`, `road_markers_mobius`: four equally spaced markers on a
     road have cross-ratio $4/3$, and so do their images under any perspective (Möbius) map.
-/

open Matrix

namespace ControlsLean.Vision

variable {K : Type*} [Field K]

/-! ### 1. Cross-ratio on the projective line $\mathbb{P}^1(K)$ -/

/-- The $2 \times 2$ bracket `[p q] = p 0 * q 1 - p 1 * q 0` of two homogeneous points. -/
def bracket2 (p q : Fin 2 → K) : K :=
  p 0 * q 1 - p 1 * q 0

/-- The cross-ratio `[p₁ p₃][p₂ p₄] / ([p₁ p₄][p₂ p₃])` of four homogeneous points of
`ℙ¹(K)`. -/
def crossRatio (p₁ p₂ p₃ p₄ : Fin 2 → K) : K :=
  bracket2 p₁ p₃ * bracket2 p₂ p₄ / (bracket2 p₁ p₄ * bracket2 p₂ p₃)

/-- Brackets scale by the determinant: `[H p, H q] = det H * [p q]`. -/
theorem bracket2_mulVec (H : Matrix (Fin 2) (Fin 2) K) (p q : Fin 2 → K) :
    bracket2 (H *ᵥ p) (H *ᵥ q) = H.det * bracket2 p q := by
  rw [det_fin_two]
  simp [bracket2, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Brackets are bilinear: `[a p, b q] = a b [p q]`. -/
theorem bracket2_smul (a b : K) (p q : Fin 2 → K) :
    bracket2 (a • p) (b • q) = a * b * bracket2 p q := by
  simp [bracket2]
  ring

private theorem mul_mul_div_mul_mul (k a b c d : K) (hk : k ≠ 0) :
    (k * a) * (k * b) / ((k * c) * (k * d)) = a * b / (c * d) := by
  rw [show (k * a) * (k * b) = (k * k) * (a * b) by ring,
    show (k * c) * (k * d) = (k * k) * (c * d) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero hk hk)

/-- **Projective invariance of the cross-ratio**: for any `H` with `det H ≠ 0`,
`CR(H p₁, H p₂; H p₃, H p₄) = CR(p₁, p₂; p₃, p₄)`. -/
theorem crossRatio_mulVec (H : Matrix (Fin 2) (Fin 2) K) (hH : H.det ≠ 0)
    (p₁ p₂ p₃ p₄ : Fin 2 → K) :
    crossRatio (H *ᵥ p₁) (H *ᵥ p₂) (H *ᵥ p₃) (H *ᵥ p₄) = crossRatio p₁ p₂ p₃ p₄ := by
  simp only [crossRatio, bracket2_mulVec]
  exact mul_mul_div_mul_mul _ _ _ _ _ hH

/-- **Well-definedness on `ℙ¹(K)`**: rescaling each homogeneous representative by a nonzero
scalar does not change the cross-ratio. -/
theorem crossRatio_smul (a₁ a₂ a₃ a₄ : K) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0)
    (h₄ : a₄ ≠ 0) (p₁ p₂ p₃ p₄ : Fin 2 → K) :
    crossRatio (a₁ • p₁) (a₂ • p₂) (a₃ • p₃) (a₄ • p₄) = crossRatio p₁ p₂ p₃ p₄ := by
  simp only [crossRatio, bracket2_smul]
  have hk : a₁ * a₂ * a₃ * a₄ ≠ 0 := by
    simp [h₁, h₂, h₃, h₄]
  rw [show a₁ * a₃ * bracket2 p₁ p₃ * (a₂ * a₄ * bracket2 p₂ p₄)
      = (a₁ * a₂ * a₃ * a₄) * (bracket2 p₁ p₃ * bracket2 p₂ p₄) by ring,
    show a₁ * a₄ * bracket2 p₁ p₄ * (a₂ * a₃ * bracket2 p₂ p₃)
      = (a₁ * a₂ * a₃ * a₄) * (bracket2 p₁ p₄ * bracket2 p₂ p₃) by ring]
  exact mul_div_mul_left _ _ hk

/-- Swapping the last two points inverts the cross-ratio. -/
theorem crossRatio_swap_34 (p₁ p₂ p₃ p₄ : Fin 2 → K) :
    crossRatio p₁ p₂ p₄ p₃ = (crossRatio p₁ p₂ p₃ p₄)⁻¹ := by
  simp only [crossRatio, inv_div]

/-! ### 2. Affine form and Möbius invariance -/

/-- Affine cross-ratio of four scalars: `(a - c)(b - d) / ((a - d)(b - c))`. -/
def crossRatioAffine (a b c d : K) : K :=
  (a - c) * (b - d) / ((a - d) * (b - c))

/-- The affine cross-ratio is the cross-ratio of the homogeneous points `[x, 1]`. -/
theorem crossRatioAffine_eq_crossRatio (a b c d : K) :
    crossRatioAffine a b c d = crossRatio ![a, 1] ![b, 1] ![c, 1] ![d, 1] := by
  simp [crossRatioAffine, crossRatio, bracket2]

/-- The Möbius (linear fractional) map `x ↦ (α x + β) / (γ x + δ)`. -/
def mobius (α β γ δ x : K) : K :=
  (α * x + β) / (γ * x + δ)

/-- In homogeneous coordinates a Möbius map is the matrix `!![α, β; γ, δ]` followed by
normalisation of the last coordinate. -/
theorem mobius_homogeneous (α β γ δ x : K) (hx : γ * x + δ ≠ 0) :
    ![mobius α β γ δ x, 1] = (γ * x + δ)⁻¹ • (!![α, β; γ, δ] *ᵥ ![x, 1]) := by
  ext i
  fin_cases i
  · simp [mobius, div_eq_inv_mul, mul_comm]
  · simp [mul_comm x γ, inv_mul_cancel₀ hx]

/-- **Möbius invariance of the affine cross-ratio**: for `α δ - β γ ≠ 0` and nonvanishing
denominators `γ x + δ` at the four points, the cross-ratio of the images equals the
cross-ratio of the originals. -/
theorem crossRatioAffine_mobius (α β γ δ : K) (hdet : α * δ - β * γ ≠ 0) (a b c d : K)
    (ha : γ * a + δ ≠ 0) (hb : γ * b + δ ≠ 0) (hc : γ * c + δ ≠ 0) (hd : γ * d + δ ≠ 0) :
    crossRatioAffine (mobius α β γ δ a) (mobius α β γ δ b) (mobius α β γ δ c)
      (mobius α β γ δ d) = crossRatioAffine a b c d := by
  have hH : (!![α, β; γ, δ] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rwa [det_fin_two_of]
  rw [crossRatioAffine_eq_crossRatio, crossRatioAffine_eq_crossRatio,
    mobius_homogeneous _ _ _ _ _ ha, mobius_homogeneous _ _ _ _ _ hb,
    mobius_homogeneous _ _ _ _ _ hc, mobius_homogeneous _ _ _ _ _ hd,
    crossRatio_smul _ _ _ _ (inv_ne_zero ha) (inv_ne_zero hb) (inv_ne_zero hc)
      (inv_ne_zero hd),
    crossRatio_mulVec _ hH]

/-! ### 3. Collinear points in the image plane and 3×3 homographies -/

/-- The $3 \times 3$ bracket `[o p q] = det [o; p; q]`. -/
def bracket3 (o p q : Fin 3 → K) : K :=
  (Matrix.of ![o, p, q]).det

/-- Cross-ratio of four image points measured from a vantage point `o`:
`[o p₁ p₃][o p₂ p₄] / ([o p₁ p₄][o p₂ p₃])`. -/
def crossRatioFrom (o p₁ p₂ p₃ p₄ : Fin 3 → K) : K :=
  bracket3 o p₁ p₃ * bracket3 o p₂ p₄ / (bracket3 o p₁ p₄ * bracket3 o p₂ p₃)

/-- The point `c 0 • u + c 1 • v` on the line through `u` and `v`, with line coordinates
`c ∈ K²`. -/
def linePt (u v : Fin 3 → K) (c : Fin 2 → K) : Fin 3 → K :=
  c 0 • u + c 1 • v

/-- Brackets of points on the line through `u, v` factor through the line coordinates:
`[o, linePt c, linePt c'] = [o u v] * [c c']`. -/
theorem bracket3_linePt (o u v : Fin 3 → K) (c c' : Fin 2 → K) :
    bracket3 o (linePt u v c) (linePt u v c') = bracket3 o u v * bracket2 c c' := by
  simp only [bracket3, bracket2, linePt]
  rw [det_fin_three, det_fin_three]
  simp
  ring

/-- **Cross-ratio of collinear image points**: for points `pᵢ = sᵢ u + tᵢ v` on the line
through `u, v`, the cross-ratio seen from any vantage point `o` off the line equals the
cross-ratio of the line coordinates `(sᵢ, tᵢ)`; in particular it is independent of `o`. -/
theorem crossRatioFrom_linePt (o u v : Fin 3 → K) (ho : bracket3 o u v ≠ 0)
    (c₁ c₂ c₃ c₄ : Fin 2 → K) :
    crossRatioFrom o (linePt u v c₁) (linePt u v c₂) (linePt u v c₃) (linePt u v c₄)
      = crossRatio c₁ c₂ c₃ c₄ := by
  simp only [crossRatioFrom, bracket3_linePt]
  exact mul_mul_div_mul_mul _ _ _ _ _ ho

/-- Brackets scale by the determinant under a homography: `[H o, H p, H q] = det H [o p q]`. -/
theorem bracket3_mulVec (H : Matrix (Fin 3) (Fin 3) K) (o p q : Fin 3 → K) :
    bracket3 (H *ᵥ o) (H *ᵥ p) (H *ᵥ q) = H.det * bracket3 o p q :=
  det_homography_three_points H o p q

/-- **Homography invariance of the cross-ratio in the image plane**: for any invertible
`3 × 3` homography `H`, moving the vantage point and the four points by `H` leaves the
cross-ratio unchanged. -/
theorem crossRatioFrom_homography (H : Matrix (Fin 3) (Fin 3) K) (hH : H.det ≠ 0)
    (o p₁ p₂ p₃ p₄ : Fin 3 → K) :
    crossRatioFrom (H *ᵥ o) (H *ᵥ p₁) (H *ᵥ p₂) (H *ᵥ p₃) (H *ᵥ p₄)
      = crossRatioFrom o p₁ p₂ p₃ p₄ := by
  simp only [crossRatioFrom, bracket3_mulVec]
  exact mul_mul_div_mul_mul _ _ _ _ _ hH

/-- A homography maps the line through `u, v` to the line through `H u, H v`, keeping line
coordinates. -/
theorem mulVec_linePt (H : Matrix (Fin 3) (Fin 3) K) (u v : Fin 3 → K) (c : Fin 2 → K) :
    H *ᵥ linePt u v c = linePt (H *ᵥ u) (H *ᵥ v) c := by
  simp [linePt, mulVec_add, mulVec_smul]

/-- **Cross-ratio of four collinear image points is a projective invariant**: let
`pᵢ = sᵢ u + tᵢ v` be four points on the line through `u, v`, and `H` any `3 × 3` matrix.
Measuring the cross-ratio of the `pᵢ` from a vantage point `o` off the line `uv`, and that of
the images `H pᵢ` from any vantage point `o'` off the image line through `H u, H v`, gives the
same value. -/
theorem crossRatio_collinear_homography (H : Matrix (Fin 3) (Fin 3) K)
    (u v o o' : Fin 3 → K) (ho : bracket3 o u v ≠ 0) (ho' : bracket3 o' (H *ᵥ u) (H *ᵥ v) ≠ 0)
    (c₁ c₂ c₃ c₄ : Fin 2 → K) :
    crossRatioFrom o' (H *ᵥ linePt u v c₁) (H *ᵥ linePt u v c₂) (H *ᵥ linePt u v c₃)
        (H *ᵥ linePt u v c₄)
      = crossRatioFrom o (linePt u v c₁) (linePt u v c₂) (linePt u v c₃) (linePt u v c₄) := by
  simp only [mulVec_linePt]
  rw [crossRatioFrom_linePt _ _ _ ho', crossRatioFrom_linePt _ _ _ ho]

/-! ### 4. Corollaries: harmonic ranges and equally spaced road markers -/

/-- **Midpoint and point at infinity are harmonic**: on the affine line, the endpoints
`[a, 1]`, `[b, 1]` (with `a ≠ b`), the midpoint `[a + b, 2]` and the point at infinity
`[1, 0]` have cross-ratio `-1`. -/
theorem crossRatio_midpoint_infinity (a b : K) (hab : a ≠ b) :
    crossRatio ![a, 1] ![b, 1] ![a + b, 2] ![1, 0] = -1 := by
  have h : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp only [crossRatio, bracket2]
  simp
  rw [show a + b - a * 2 = -(a + b - b * 2) by ring, neg_div,
    div_self (by rwa [show a + b - b * 2 = -(b - a) by ring, neg_ne_zero])]

/-- **Vanishing points and harmonic conjugates**: under any invertible homography `H` of the
line, the images of the two endpoints of a segment, of its midpoint and of the point at
infinity (the vanishing point) still have cross-ratio `-1`. -/
theorem crossRatio_harmonic_homography (H : Matrix (Fin 2) (Fin 2) K) (hH : H.det ≠ 0)
    (a b : K) (hab : a ≠ b) :
    crossRatio (H *ᵥ ![a, 1]) (H *ᵥ ![b, 1]) (H *ᵥ ![a + b, 2]) (H *ᵥ ![1, 0]) = -1 := by
  rw [crossRatio_mulVec H hH, crossRatio_midpoint_infinity a b hab]

/-- Four equally spaced points `x, x + h, x + 2h, x + 3h` with `h ≠ 0` have cross-ratio
`4 / 3`. -/
theorem crossRatioAffine_equally_spaced (x h : K) (hh : h ≠ 0) :
    crossRatioAffine x (x + h) (x + 2 * h) (x + 3 * h) = 4 / 3 := by
  have hh2 : h * h ≠ 0 := mul_ne_zero hh hh
  unfold crossRatioAffine
  rw [show (x - (x + 2 * h)) * (x + h - (x + 3 * h)) = (h * h) * 4 by ring,
    show (x - (x + 3 * h)) * (x + h - (x + 2 * h)) = (h * h) * 3 by ring]
  exact mul_div_mul_left _ _ hh2

/-- **Equally spaced road markers in perspective**: four equally spaced markers on a road,
imaged by any perspective map `x ↦ (α x + β) / (γ x + δ)` with `α δ - β γ ≠ 0` (and all four
markers in front of the camera, `γ x + δ ≠ 0`), have image positions with cross-ratio `4 / 3`,
even though the image spacings are no longer equal. -/
theorem road_markers_mobius (α β γ δ : K) (hdet : α * δ - β * γ ≠ 0) (x h : K) (hh : h ≠ 0)
    (h₀ : γ * x + δ ≠ 0) (h₁ : γ * (x + h) + δ ≠ 0) (h₂ : γ * (x + 2 * h) + δ ≠ 0)
    (h₃ : γ * (x + 3 * h) + δ ≠ 0) :
    crossRatioAffine (mobius α β γ δ x) (mobius α β γ δ (x + h)) (mobius α β γ δ (x + 2 * h))
      (mobius α β γ δ (x + 3 * h)) = 4 / 3 := by
  rw [crossRatioAffine_mobius α β γ δ hdet _ _ _ _ h₀ h₁ h₂ h₃,
    crossRatioAffine_equally_spaced x h hh]

end ControlsLean.Vision
