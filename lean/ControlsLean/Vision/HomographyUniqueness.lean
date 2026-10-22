/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ControlsLean.Vision.Homography

/-!
# Four-Point Planar Homography Uniqueness and Projective Frame Rigidity

This module formalizes the fundamental uniqueness and rigidity theorems for planar projective
transformations (homographies) in $\mathbb{P}^2(K)$ (Hartley & Zisserman, *Multiple View Geometry*,
Theorem 2.10 & Section 4.1; Semple & Kneebone, *Algebraic Projective Geometry*, Chapter IV):

A planar projective transformation $H \in \mathrm{PGL}(3, K)$ has 8 degrees of freedom (9 matrix
entries minus 1 overall homogeneous scale factor). Each point-to-point projective correspondence
$x'_i \propto H x_i$ imposes 2 independent constraints, so 4 points in general position (no three
collinear) uniquely determine $H$ up to a single common nonzero scalar factor.

### Main Results Proved:
1. **Standard Projective Frame (`e₀`, `e₁`, `e₂`, `e₃`)**:
   - The four canonical frame points `e₀ = ![1, 0, 0]`, `e₁ = ![0, 1, 0]`, `e₂ = ![0, 0, 1]`,
     and unit point `e₃ = ![1, 1, 1]` satisfy `e₀ + e₁ + e₂ = e₃` and are in general position
     (every triple has determinant $\pm 1$).
2. **Diagonal Scaling from 3 Basis Points (`eq_diagonal_of_fixes_basis` / `homography_Arena_diagonal`)**:
   - If $H \in M_3(K)$ fixes the three standard basis rays up to scalars
     ($H e_i = s_i e_i$ for $i = 0, 1, 2$), then $H = \mathrm{diag}(s_0, s_1, s_2)$.
3. **Scalar Rigidity on the 4-Point Canonical Frame (`eq_smul_one_of_fixes_canonical_frame`)**:
   - If $H$ fixes $e_0, e_1, e_2$ with scalars $s_0, s_1, s_2$ and also fixes
     the fourth frame point $e_3 = [1, 1, 1]^\top$ with scalar $s_3$ ($H e_3 = s_3 e_3$),
     then $s_0 = s_1 = s_2 = s_3$ and $H = s_3 I_3$.
4. **Uniqueness of Homographies on the Canonical Frame (`homography_unique_on_canonical_frame`)**:
   - If $H_1, H_2 \in M_3(K)$ with $H_2$ invertible satisfy $H_1 e_i = s_i H_2 e_i$ for
     $i \in \{0, 1, 2, 3\}$, then $s_0 = s_1 = s_2 = s_3$ and $H_1 = s_3 H_2$.
5. **General Four-Point Projective Frame Rigidity (`homography_unique_four_points`)**:
   - For any 4-point projective frame $(p_0, p_1, p_2, p_3)$ related to $(e_0, e_1, e_2, e_3)$ by an
     invertible change-of-basis matrix $B$ (or via general position $p_3 = c_0 p_0 + c_1 p_1 + c_2 p_2$),
     if $H p_i = s_i p_i$ for $i \in \{0, 1, 2, 3\}$, then $s_0 = s_1 = s_2 = s_3$
     and $H = s_3 I_3$.
6. **Two Homographies Agreeing on Four General Points (`two_homographies_eq_smul_of_four_points`)**:
   - Any two homographies $H_1, H_2$ (with $H_2$ invertible) that map a 4-point projective frame
     $(p_0, p_1, p_2, p_3)$ to the same projective rays differ by a single global scalar:
     $H_1 = s_3 H_2$.
-/

open Matrix

namespace ControlsLean.Vision

section CommRing

variable {K : Type*} [CommRing K]

/-! ### 1. The Standard Projective Frame in $\mathbb{P}^2(K)$ -/

/-- First standard projective frame point `e₀ = [1, 0, 0]ᵀ`. -/
def e₀ : Fin 3 → K := ![1, 0, 0]

/-- Second standard projective frame point `e₁ = [0, 1, 0]ᵀ`. -/
def e₁ : Fin 3 → K := ![0, 1, 0]

/-- Third standard projective frame point `e₂ = [0, 0, 1]ᵀ`. -/
def e₂ : Fin 3 → K := ![0, 0, 1]

/-- Fourth canonical (unit) projective frame point `e₃ = [1, 1, 1]ᵀ`. -/
def e₃ : Fin 3 → K := ![1, 1, 1]

/-- Indexed family of the three standard basis vectors in `Fin 3 → K`. -/
def stdBasis : Fin 3 → (Fin 3 → K)
  | 0 => e₀
  | 1 => e₁
  | 2 => e₂

@[simp] theorem stdBasis_zero : (stdBasis 0 : Fin 3 → K) = e₀ := rfl
@[simp] theorem stdBasis_one : (stdBasis 1 : Fin 3 → K) = e₁ := rfl
@[simp] theorem stdBasis_two : (stdBasis 2 : Fin 3 → K) = e₂ := rfl

/-- The unit frame point `e₃` is the sum of the three standard basis points `e₀ + e₁ + e₂`. -/
theorem e₀_add_e₁_add_e₂ : (e₀ : Fin 3 → K) + e₁ + e₂ = e₃ := by
  ext i
  fin_cases i <;> simp [e₀, e₁, e₂, e₃]

/-- General linear combination of the three standard basis points `e₀, e₁, e₂`. -/
theorem smul_e₀_add_smul_e₁_add_smul_e₂ (c₀ c₁ c₂ : K) :
    c₀ • (e₀ : Fin 3 → K) + c₁ • e₁ + c₂ • e₂ = ![c₀, c₁, c₂] := by
  ext i
  fin_cases i <;> simp [e₀, e₁, e₂]

/-- General position of `(e₀, e₁, e₂)`: their determinant is `1`. -/
theorem det_e₀_e₁_e₂ : (Matrix.of ![(e₀ : Fin 3 → K), e₁, e₂]).det = 1 := by
  rw [det_fin_three]
  simp [e₀, e₁, e₂]

/-- General position of `(e₀, e₁, e₃)`: their determinant is `1`. -/
theorem det_e₀_e₁_e₃ : (Matrix.of ![(e₀ : Fin 3 → K), e₁, e₃]).det = 1 := by
  rw [det_fin_three]
  simp [e₀, e₁, e₃]

/-- General position of `(e₀, e₂, e₃)`: their determinant is `-1`. -/
theorem det_e₀_e₂_e₃ : (Matrix.of ![(e₀ : Fin 3 → K), e₂, e₃]).det = -1 := by
  rw [det_fin_three]
  simp [e₀, e₂, e₃]

/-- General position of `(e₁, e₂, e₃)`: their determinant is `1`. -/
theorem det_e₁_e₂_e₃ : (Matrix.of ![(e₁ : Fin 3 → K), e₂, e₃]).det = 1 := by
  rw [det_fin_three]
  simp [e₁, e₂, e₃]

/-- Action of a $3 \times 3$ matrix `H` on `e₀` extracts its first column. -/
theorem mulVec_e₀ (H : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (H *ᵥ e₀) i = H i 0 := by
  simp [e₀, mulVec, dotProduct, Fin.sum_univ_three]

/-- Action of a $3 \times 3$ matrix `H` on `e₁` extracts its second column. -/
theorem mulVec_e₁ (H : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (H *ᵥ e₁) i = H i 1 := by
  simp [e₁, mulVec, dotProduct, Fin.sum_univ_three]

/-- Action of a $3 \times 3$ matrix `H` on `e₂` extracts its third column. -/
theorem mulVec_e₂ (H : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (H *ᵥ e₂) i = H i 2 := by
  simp [e₂, mulVec, dotProduct, Fin.sum_univ_three]

/-- Action of a $3 \times 3$ matrix `H` on `e₃` is the row sum of `H`. -/
theorem mulVec_e₃ (H : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (H *ᵥ e₃) i = H i 0 + H i 1 + H i 2 := by
  simp [e₃, mulVec, dotProduct, Fin.sum_univ_three]

/-! ### 2. Diagonal Scaling from Three Basis Points -/

/-- **Diagonal Scaling from 3 Basis Points**:
If $H \in M_3(K)$ scales each standard basis vector $e_0, e_1, e_2$ by $s_0, s_1, s_2$,
then $H$ is the diagonal matrix $\mathrm{diag}(s_0, s_1, s_2)$. -/
theorem eq_diagonal_of_fixes_basis (H : Matrix (Fin 3) (Fin 3) K) (s : Fin 3 → K)
    (h₀ : H *ᵥ e₀ = s 0 • e₀)
    (h₁ : H *ᵥ e₁ = s 1 • e₁)
    (h₂ : H *ᵥ e₂ = s 2 • e₂) :
    H = Matrix.diagonal s := by
  ext i j
  fin_cases j
  · have hi := congr_fun h₀ i
    rw [mulVec_e₀] at hi
    fin_cases i <;> simpa [e₀, diagonal] using hi
  · have hi := congr_fun h₁ i
    rw [mulVec_e₁] at hi
    fin_cases i <;> simpa [e₁, diagonal] using hi
  · have hi := congr_fun h₂ i
    rw [mulVec_e₂] at hi
    fin_cases i <;> simpa [e₂, diagonal] using hi

/-- Indexed-family formulation of **Diagonal Scaling from 3 Basis Points** (`homography_Arena_diagonal`):
If $H *ᵥ \mathrm{stdBasis}(i) = s_i \cdot \mathrm{stdBasis}(i)$ for all $i \in \mathrm{Fin}\ 3$,
then $H = \mathrm{Matrix.diagonal}\ s$. -/
theorem homography_Arena_diagonal (H : Matrix (Fin 3) (Fin 3) K) (s : Fin 3 → K)
    (h : ∀ i : Fin 3, H *ᵥ stdBasis i = s i • stdBasis i) :
    H = Matrix.diagonal s :=
  eq_diagonal_of_fixes_basis H s (h 0) (h 1) (h 2)

/-! ### 3. Scalar Matrix Rigidity from the Four-Point Canonical Frame -/

/-- If $H$ fixes $e_0, e_1, e_2, e_3$ up to scalars $s_0, s_1, s_2, s_3$,
then all four scalars are equal: $s_0 = s_3$, $s_1 = s_3$, and $s_2 = s_3$. -/
theorem scalars_eq_of_fixes_canonical_frame (H : Matrix (Fin 3) (Fin 3) K)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ e₀ = s₀ • e₀)
    (h₁ : H *ᵥ e₁ = s₁ • e₁)
    (h₂ : H *ᵥ e₂ = s₂ • e₂)
    (h₃ : H *ᵥ e₃ = s₃ • e₃) :
    s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃ := by
  have hsum : H *ᵥ e₃ = s₀ • e₀ + s₁ • e₁ + s₂ • e₂ := by
    rw [← e₀_add_e₁_add_e₂, mulVec_add, mulVec_add, h₀, h₁, h₂]
  rw [h₃] at hsum
  have c0 := congr_fun hsum 0
  have c1 := congr_fun hsum 1
  have c2 := congr_fun hsum 2
  simp [e₀, e₁, e₂, e₃] at c0 c1 c2
  exact ⟨c0.symm, c1.symm, c2.symm⟩

/-- **Scalar Matrix from 4 Canonical Frame Points**:
If $H \in M_3(K)$ fixes the three basis points $e_0, e_1, e_2$ with scalars $s_0, s_1, s_2$
and fixes the unit frame point $e_3 = [1, 1, 1]^\top$ with scalar $s_3$, then all four scalars
coincide and $H = s_3 \cdot 1$ is a scalar multiple of the identity matrix. -/
theorem eq_smul_one_of_fixes_canonical_frame (H : Matrix (Fin 3) (Fin 3) K)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ e₀ = s₀ • e₀)
    (h₁ : H *ᵥ e₁ = s₁ • e₁)
    (h₂ : H *ᵥ e₂ = s₂ • e₂)
    (h₃ : H *ᵥ e₃ = s₃ • e₃) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H = s₃ • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hscalars := scalars_eq_of_fixes_canonical_frame H s₀ s₁ s₂ s₃ h₀ h₁ h₂ h₃
  rcases hscalars with ⟨hs₀, hs₁, hs₂⟩
  refine ⟨⟨hs₀, hs₁, hs₂⟩, ?_⟩
  rw [hs₀] at h₀
  rw [hs₁] at h₁
  rw [hs₂] at h₂
  have hdiag := eq_diagonal_of_fixes_basis H (fun _ => s₃) h₀ h₁ h₂
  rw [hdiag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, one_apply]

/-! ### 4. Two Homographies Agreeing on the Canonical Frame -/

/-- Helper lemma: if `H₂_inv * H₂ = 1` and `H₁ *ᵥ p = c • (H₂ *ᵥ p)`, then
`(H₂_inv * H₁) *ᵥ p = c • p`. -/
theorem mul_inv_fixes_point_of_eq_smul (H₁ H₂ H₂_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H₂_inv * H₂ = 1) (p : Fin 3 → K) (c : K)
    (hp : H₁ *ᵥ p = c • (H₂ *ᵥ p)) :
    (H₂_inv * H₁) *ᵥ p = c • p := by
  rw [← mulVec_mulVec, hp, mulVec_smul, mulVec_mulVec, hinv, one_mulVec]

/-- **Uniqueness of Homographies on the Canonical Frame** (Hartley & Zisserman Section 4.1):
If $H_1, H_2 \in M_3(K)$ with $H_2$ invertible (`H₂_inv * H₂ = 1`) map the four canonical frame
points $e_0, e_1, e_2, e_3$ to the same projective rays ($H_1 e_i = s_i H_2 e_i$), then
$s_0 = s_1 = s_2 = s_3$ and $H_1 = s_3 \cdot H_2$. -/
theorem homography_unique_on_canonical_frame (H₁ H₂ H₂_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H₂_inv * H₂ = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H₁ *ᵥ e₀ = s₀ • (H₂ *ᵥ e₀))
    (h₁ : H₁ *ᵥ e₁ = s₁ • (H₂ *ᵥ e₁))
    (h₂ : H₁ *ᵥ e₂ = s₂ • (H₂ *ᵥ e₂))
    (h₃ : H₁ *ᵥ e₃ = s₃ • (H₂ *ᵥ e₃)) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H₁ = s₃ • H₂ := by
  have m₀ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv e₀ s₀ h₀
  have m₁ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv e₁ s₁ h₁
  have m₂ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv e₂ s₂ h₂
  have m₃ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv e₃ s₃ h₃
  have hM := eq_smul_one_of_fixes_canonical_frame (H₂_inv * H₁) s₀ s₁ s₂ s₃ m₀ m₁ m₂ m₃
  rcases hM with ⟨hscalars, hM_eq⟩
  refine ⟨hscalars, ?_⟩
  have hinv_right : H₂ * H₂_inv = 1 := mul_eq_one_comm.mp hinv
  calc
    H₁ = 1 * H₁ := (Matrix.one_mul H₁).symm
    _ = (H₂ * H₂_inv) * H₁ := by rw [hinv_right]
    _ = H₂ * (H₂_inv * H₁) := Matrix.mul_assoc H₂ H₂_inv H₁
    _ = H₂ * (s₃ • 1) := by rw [hM_eq]
    _ = s₃ • H₂ := by rw [Matrix.mul_smul, Matrix.mul_one]

/-! ### 5. General Four-Point Projective Frame Rigidity -/

/-- Conjugation lemma: if $B_{\mathrm{inv}} B = 1$ and $H$ scales $B e_i$ by $s_i$,
then the conjugated matrix $B_{\mathrm{inv}} H B$ scales $e_i$ by $s_i$. -/
theorem conj_fixes_of_fixes_image (H B B_inv : Matrix (Fin 3) (Fin 3) K)
    (hB : B_inv * B = 1) (v : Fin 3 → K) (c : K)
    (hv : H *ᵥ (B *ᵥ v) = c • (B *ᵥ v)) :
    (B_inv * H * B) *ᵥ v = c • v := by
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_smul, mulVec_mulVec, hB, one_mulVec]

/-- **General Four-Point Projective Frame Rigidity** (Hartley & Zisserman Theorem 2.10):
Let $p_i = B e_i$ ($i = 0, 1, 2, 3$) be any four points in projective general position represented
via an invertible projective basis matrix $B$ (`B_inv * B = 1`). If a homography matrix $H \in M_3(K)$
fixes all four points up to scalars ($H p_i = s_i p_i$ for $i = 0, 1, 2, 3$), then
$s_0 = s_1 = s_2 = s_3$ and $H = s_3 \cdot 1$. -/
theorem homography_unique_four_points (H B B_inv : Matrix (Fin 3) (Fin 3) K)
    (hB : B_inv * B = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ (B *ᵥ e₀) = s₀ • (B *ᵥ e₀))
    (h₁ : H *ᵥ (B *ᵥ e₁) = s₁ • (B *ᵥ e₁))
    (h₂ : H *ᵥ (B *ᵥ e₂) = s₂ • (B *ᵥ e₂))
    (h₃ : H *ᵥ (B *ᵥ e₃) = s₃ • (B *ᵥ e₃)) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H = s₃ • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have c₀ := conj_fixes_of_fixes_image H B B_inv hB e₀ s₀ h₀
  have c₁ := conj_fixes_of_fixes_image H B B_inv hB e₁ s₁ h₁
  have c₂ := conj_fixes_of_fixes_image H B B_inv hB e₂ s₂ h₂
  have c₃ := conj_fixes_of_fixes_image H B B_inv hB e₃ s₃ h₃
  have hM := eq_smul_one_of_fixes_canonical_frame (B_inv * H * B) s₀ s₁ s₂ s₃ c₀ c₁ c₂ c₃
  rcases hM with ⟨hscalars, hM_eq⟩
  refine ⟨hscalars, ?_⟩
  have hB_right : B * B_inv = 1 := mul_eq_one_comm.mp hB
  calc
    H = 1 * H * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
    _ = (B * B_inv) * H * (B * B_inv) := by rw [hB_right]
    _ = B * (B_inv * H * B) * B_inv := by simp only [Matrix.mul_assoc]
    _ = B * (s₃ • 1) * B_inv := by rw [hM_eq]
    _ = s₃ • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB_right]

/-- **Two Homographies Agreeing on a General Four-Point Projective Frame**:
If $H_1, H_2 \in M_3(K)$ (with $H_2$ invertible, `H₂_inv * H₂ = 1`) agree up to projective scalars
on the four points $p_i = B e_i$ ($i = 0, 1, 2, 3$) of an arbitrary projective frame (`B_inv * B = 1`),
i.e., $H_1 p_i = s_i H_2 p_i$, then $s_0 = s_1 = s_2 = s_3$ and
$H_1 = s_3 \cdot H_2$. -/
theorem two_homographies_eq_smul_of_four_points (H₁ H₂ H₂_inv B B_inv : Matrix (Fin 3) (Fin 3) K)
    (hinv : H₂_inv * H₂ = 1) (hB : B_inv * B = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H₁ *ᵥ (B *ᵥ e₀) = s₀ • (H₂ *ᵥ (B *ᵥ e₀)))
    (h₁ : H₁ *ᵥ (B *ᵥ e₁) = s₁ • (H₂ *ᵥ (B *ᵥ e₁)))
    (h₂ : H₁ *ᵥ (B *ᵥ e₂) = s₂ • (H₂ *ᵥ (B *ᵥ e₂)))
    (h₃ : H₁ *ᵥ (B *ᵥ e₃) = s₃ • (H₂ *ᵥ (B *ᵥ e₃))) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H₁ = s₃ • H₂ := by
  have m₀ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv (B *ᵥ e₀) s₀ h₀
  have m₁ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv (B *ᵥ e₁) s₁ h₁
  have m₂ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv (B *ᵥ e₂) s₂ h₂
  have m₃ := mul_inv_fixes_point_of_eq_smul H₁ H₂ H₂_inv hinv (B *ᵥ e₃) s₃ h₃
  have hM := homography_unique_four_points (H₂_inv * H₁) B B_inv hB s₀ s₁ s₂ s₃ m₀ m₁ m₂ m₃
  rcases hM with ⟨hscalars, hM_eq⟩
  refine ⟨hscalars, ?_⟩
  have hinv_right : H₂ * H₂_inv = 1 := mul_eq_one_comm.mp hinv
  calc
    H₁ = 1 * H₁ := (Matrix.one_mul H₁).symm
    _ = (H₂ * H₂_inv) * H₁ := by rw [hinv_right]
    _ = H₂ * (H₂_inv * H₁) := Matrix.mul_assoc H₂ H₂_inv H₁
    _ = H₂ * (s₃ • 1) := by rw [hM_eq]
    _ = s₃ • H₂ := by rw [Matrix.mul_smul, Matrix.mul_one]

/-! ### 6. Explicit Frame Construction from Four Points in General Position -/

/-- Given three points $p_0, p_1, p_2 \in K^3$ and nonzero coefficients $c_0, c_1, c_2 \in K$
such that $p_3 = c_0 p_0 + c_1 p_1 + c_2 p_2$, `frameBasisMatrix` is the $3 \times 3$ matrix
whose columns are $c_0 p_0, c_1 p_1, c_2 p_2$. It maps the canonical frame $(e_0, e_1, e_2, e_3)$
to $(c_0 p_0, c_1 p_1, c_2 p_2, p_3)$. -/
def frameBasisMatrix (p₀ p₁ p₂ : Fin 3 → K) (c₀ c₁ c₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  (Matrix.of ![c₀ • p₀, c₁ • p₁, c₂ • p₂])ᵀ

theorem frameBasisMatrix_mulVec_e₀ (p₀ p₁ p₂ : Fin 3 → K) (c₀ c₁ c₂ : K) :
    frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂ *ᵥ e₀ = c₀ • p₀ := by
  ext i
  rw [mulVec_e₀]
  rfl

theorem frameBasisMatrix_mulVec_e₁ (p₀ p₁ p₂ : Fin 3 → K) (c₀ c₁ c₂ : K) :
    frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂ *ᵥ e₁ = c₁ • p₁ := by
  ext i
  rw [mulVec_e₁]
  rfl

theorem frameBasisMatrix_mulVec_e₂ (p₀ p₁ p₂ : Fin 3 → K) (c₀ c₁ c₂ : K) :
    frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂ *ᵥ e₂ = c₂ • p₂ := by
  ext i
  rw [mulVec_e₂]
  rfl

theorem frameBasisMatrix_mulVec_e₃ (p₀ p₁ p₂ p₃ : Fin 3 → K) (c₀ c₁ c₂ : K)
    (hp₃ : p₃ = c₀ • p₀ + c₁ • p₁ + c₂ • p₂) :
    frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂ *ᵥ e₃ = p₃ := by
  rw [← e₀_add_e₁_add_e₂, mulVec_add, mulVec_add,
      frameBasisMatrix_mulVec_e₀, frameBasisMatrix_mulVec_e₁, frameBasisMatrix_mulVec_e₂, hp₃]

/-- Determinant of `frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂` factors as
$c_0 c_1 c_2 \det [p_0, p_1, p_2]$. -/
theorem det_frameBasisMatrix (p₀ p₁ p₂ : Fin 3 → K) (c₀ c₁ c₂ : K) :
    (frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂).det =
      c₀ * c₁ * c₂ * (Matrix.of ![p₀, p₁, p₂]).det := by
  unfold frameBasisMatrix
  rw [det_transpose, det_fin_three (Matrix.of ![c₀ • p₀, c₁ • p₁, c₂ • p₂]),
      det_fin_three (Matrix.of ![p₀, p₁, p₂])]
  simp
  ring

end CommRing

section Field

variable {K : Type*} [Field K]

/-- **Coordinate-Free Four-Point Homography Rigidity over a Field**:
Let $p_0, p_1, p_2, p_3 \in K^3$ be four points such that $p_3 = c_0 p_0 + c_1 p_1 + c_2 p_2$
and `frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂` has left inverse `B_inv` (equivalently, $c_0, c_1, c_2 \neq 0$
and $p_0, p_1, p_2$ are linearly independent, meaning no three of $p_0, p_1, p_2, p_3$ are collinear).
If $H p_i = s_i p_i$ for $i = 0, 1, 2, 3$, then
$s_0 = s_1 = s_2 = s_3$ and $H = s_3 \cdot 1$. -/
theorem homography_rigidity_of_general_position (H : Matrix (Fin 3) (Fin 3) K)
    (p₀ p₁ p₂ p₃ : Fin 3 → K) (c₀ c₁ c₂ : K)
    (hp₃ : p₃ = c₀ • p₀ + c₁ • p₁ + c₂ • p₂)
    (B_inv : Matrix (Fin 3) (Fin 3) K)
    (hB : B_inv * frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂ = 1)
    (s₀ s₁ s₂ s₃ : K)
    (h₀ : H *ᵥ p₀ = s₀ • p₀)
    (h₁ : H *ᵥ p₁ = s₁ • p₁)
    (h₂ : H *ᵥ p₂ = s₂ • p₂)
    (h₃ : H *ᵥ p₃ = s₃ • p₃) :
    (s₀ = s₃ ∧ s₁ = s₃ ∧ s₂ = s₃) ∧ H = s₃ • (1 : Matrix (Fin 3) (Fin 3) K) := by
  let B := frameBasisMatrix p₀ p₁ p₂ c₀ c₁ c₂
  have hb₀ : H *ᵥ (B *ᵥ e₀) = s₀ • (B *ᵥ e₀) := by
    rw [frameBasisMatrix_mulVec_e₀, mulVec_smul, h₀, smul_comm]
  have hb₁ : H *ᵥ (B *ᵥ e₁) = s₁ • (B *ᵥ e₁) := by
    rw [frameBasisMatrix_mulVec_e₁, mulVec_smul, h₁, smul_comm]
  have hb₂ : H *ᵥ (B *ᵥ e₂) = s₂ • (B *ᵥ e₂) := by
    rw [frameBasisMatrix_mulVec_e₂, mulVec_smul, h₂, smul_comm]
  have hb₃ : H *ᵥ (B *ᵥ e₃) = s₃ • (B *ᵥ e₃) := by
    rw [frameBasisMatrix_mulVec_e₃ p₀ p₁ p₂ p₃ c₀ c₁ c₂ hp₃, h₃]
  exact homography_unique_four_points H B B_inv hB s₀ s₁ s₂ s₃ hb₀ hb₁ hb₂ hb₃

end Field

end ControlsLean.Vision
