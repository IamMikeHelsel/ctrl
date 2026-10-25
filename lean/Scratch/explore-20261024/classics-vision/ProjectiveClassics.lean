import Mathlib

/-!
# Desargues (1639/1648) and the Möbius/Chasles cross-ratio, in homogeneous coordinates

Points and lines of the projective plane are vectors in `Fin 3 → K` (any commutative ring);
`l ⬝ᵥ p = 0` is incidence, `p ⨯₃ q` is the line through `p, q`.

* `desargues`: if `a' = a + λ o`, `b' = b + μ o`, `c' = c + ν o` (triangles in perspective from
  `o`), then explicit points `X_ab = μ a - λ b` etc. lie on both `ab` and `a'b'`, and the three
  are collinear (`det = 0`) — the axis of perspectivity.
* `pencilCrossRatio`: cross-ratio of the pencil of four lines `op, oq, or, os` (Möbius 1827 /
  Chasles 1852), invariant under every invertible homography `H` and under rescaling of
  homogeneous representatives.
-/

open Matrix

namespace ProjectiveClassics

section Desargues

variable {K : Type*} [CommRing K]

theorem on_line_ab (a b : Fin 3 → K) (l m : K) : (a ⨯₃ b) ⬝ᵥ (m • a - l • b) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm, dot_self_cross,
    dotProduct_comm, dot_cross_self]; simp

theorem on_line_a'b' (a b o : Fin 3 → K) (l m : K) :
    ((a + l • o) ⨯₃ (b + m • o)) ⬝ᵥ (m • a - l • b) = 0 := by
  have : m • a - l • b = m • (a + l • o) - l • (b + m • o) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, mul_comm]; abel
  rw [this]; exact on_line_ab _ _ l m

/-- **Desargues' theorem** (perspective from a point ⇒ perspective from a line). -/
theorem desargues (a b c o : Fin 3 → K) (l m n : K) :
    -- the three side-intersection points
    let X := m • a - l • b
    let Y := n • b - m • c
    let Z := l • c - n • a
    ((a ⨯₃ b) ⬝ᵥ X = 0 ∧ ((a + l • o) ⨯₃ (b + m • o)) ⬝ᵥ X = 0) ∧
    ((b ⨯₃ c) ⬝ᵥ Y = 0 ∧ ((b + m • o) ⨯₃ (c + n • o)) ⬝ᵥ Y = 0) ∧
    ((c ⨯₃ a) ⬝ᵥ Z = 0 ∧ ((c + n • o) ⨯₃ (a + l • o)) ⬝ᵥ Z = 0) ∧
    det (of ![X, Y, Z]) = 0 := by
  intro X Y Z
  refine ⟨⟨on_line_ab _ _ _ _, on_line_a'b' _ _ _ _ _⟩, ⟨on_line_ab _ _ _ _,
    on_line_a'b' _ _ _ _ _⟩, ⟨on_line_ab _ _ _ _, on_line_a'b' _ _ _ _ _⟩, ?_⟩
  simp only [X, Y, Z, det_fin_three]
  simp; ring

end Desargues

section CrossRatio

variable {K : Type*} [Field K]

/-- Cross-ratio of the pencil of lines `op, oq, or, os`. -/
noncomputable def pencilCrossRatio (o p q r s : Fin 3 → K) : K :=
  det (of ![o, p, r]) * det (of ![o, q, s]) / (det (of ![o, p, s]) * det (of ![o, q, r]))

theorem det_mulVec (H : Matrix (Fin 3) (Fin 3) K) (u v w : Fin 3 → K) :
    det (of ![H *ᵥ u, H *ᵥ v, H *ᵥ w]) = det H * det (of ![u, v, w]) := by
  have : (of ![H *ᵥ u, H *ᵥ v, H *ᵥ w] : Matrix (Fin 3) (Fin 3) K) = of ![u, v, w] * Hᵀ := by
    ext i j; fin_cases i <;> simp [mulVec, mul_apply, dotProduct, mul_comm]
  rw [this, det_mul, det_transpose, mul_comm]

/-- **Projective invariance of the cross-ratio** (Möbius 1827). -/
theorem pencilCrossRatio_homography (H : Matrix (Fin 3) (Fin 3) K) (hH : det H ≠ 0)
    (o p q r s : Fin 3 → K) :
    pencilCrossRatio (H *ᵥ o) (H *ᵥ p) (H *ᵥ q) (H *ᵥ r) (H *ᵥ s) =
      pencilCrossRatio o p q r s := by
  simp only [pencilCrossRatio, det_mulVec]
  by_cases h : det (of ![o, p, s]) * det (of ![o, q, r]) = 0
  · have : det H * det (of ![o, p, s]) * (det H * det (of ![o, q, r])) = 0 := by
      rw [show det H * det (of ![o, p, s]) * (det H * det (of ![o, q, r])) =
        det H ^ 2 * (det (of ![o, p, s]) * det (of ![o, q, r])) by ring, h, mul_zero]
    rw [this, h, div_zero, div_zero]
  · field_simp

/-- Independence of the homogeneous representatives. -/
theorem pencilCrossRatio_smul (o p q r s : Fin 3 → K) (α β γ δ ε : K) (hα : α ≠ 0)
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    pencilCrossRatio (α • o) (β • p) (γ • q) (δ • r) (ε • s) = pencilCrossRatio o p q r s := by
  have e : ∀ (a b c : K) (u v w : Fin 3 → K),
      det (of ![a • u, b • v, c • w]) = a * b * c * det (of ![u, v, w]) := fun a b c u v w => by
    simp [det_fin_three]; ring
  simp only [pencilCrossRatio, e]
  by_cases h : det (of ![o, p, s]) * det (of ![o, q, r]) = 0
  · rcases mul_eq_zero.1 h with h | h <;> simp [h]
  · rcases mul_ne_zero_iff.1 h with ⟨h1, h2⟩
    field_simp

end CrossRatio

end ProjectiveClassics
