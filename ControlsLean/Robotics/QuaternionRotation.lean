/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Unit Quaternions as 3D Rotations

For a quaternion $q = w + x i + y j + z k \in \mathbb{H}$ the sandwich map
$\operatorname{rot}_q(v) = q v \bar q$ acts on pure quaternions $v$ (vectors in
$\mathbb{R}^3$). For unit $q$ it is norm-preserving, given by a matrix in $\mathrm{SO}(3)$,
multiplicative in $q$, and invariant under $q \mapsto -q$. (Surjectivity onto
$\mathrm{SO}(3)$ and kernel exactly $\{\pm 1\}$ are not proved here.)

## Main results

- `re_rotate`: $\operatorname{Re}(q v \bar q) = |q|^2 \operatorname{Re}(v)$; in particular
  `rotate_re_eq_zero`: the sandwich map sends pure quaternions to pure quaternions.
- `normSq_rotate`: $|q v \bar q|^2 = |q|^4 |v|^2$.
- `norm_rotate`: $\|q v \bar q\| = \|v\|$ for $\|q\| = 1$.
- `rotate_mul`: composition homomorphism
  $\operatorname{rot}_{q_1 q_2} = \operatorname{rot}_{q_1} \circ \operatorname{rot}_{q_2}$.
- `rotate_neg`: double cover $\operatorname{rot}_{-q} = \operatorname{rot}_q$.
- `rotMatrix`: the standard $3 \times 3$ rotation matrix of $q$,
  $$R(q) = \begin{bmatrix}
    1 - 2(y^2 + z^2) & 2(xy - wz) & 2(xz + wy) \\
    2(xy + wz) & 1 - 2(x^2 + z^2) & 2(yz - wx) \\
    2(xz - wy) & 2(yz + wx) & 1 - 2(x^2 + y^2)
  \end{bmatrix}.$$
- `rotMatrix_transpose_mul_self`, `rotMatrix_mul_transpose_self`, `det_rotMatrix`:
  $R(q)^\top R(q) = R(q) R(q)^\top = I_3$ and $\det R(q) = 1$ for $\|q\| = 1$;
  packaged as `rotMatrix_mem_specialOrthogonalGroup`: $R(q) \in \mathrm{SO}(3)$.
- `rotMatrix_mulVec_imVec`: $R(q)$ acts as the sandwich map on imaginary parts,
  $R(q)\,\operatorname{im}(v) = \operatorname{im}(q v \bar q)$ for $\|q\| = 1$.
- `hasDerivAt_normSq_kinematics`: along quaternion kinematics
  $\dot q = \tfrac12 q \omega$ with pure angular velocity $\omega$,
  $\tfrac{d}{dt}|q|^2 = 0$.
-/

namespace ControlsLean.Robotics

open Quaternion Matrix

/-- The sandwich map $v \mapsto q v \bar q$. -/
def rotate (q v : ℍ[ℝ]) : ℍ[ℝ] := q * v * star q

/-- Imaginary part of a quaternion as a vector in $\mathbb{R}^3$. -/
def imVec (v : ℍ[ℝ]) : Fin 3 → ℝ := ![v.imI, v.imJ, v.imK]

/-- Real part of the sandwich: $\operatorname{Re}(q v \bar q) = |q|^2 \operatorname{Re}(v)$. -/
theorem re_rotate (q v : ℍ[ℝ]) : (rotate q v).re = normSq q * v.re := by
  simp [rotate, normSq_def']
  ring

/-- The sandwich map preserves pure quaternions. -/
theorem rotate_re_eq_zero (q : ℍ[ℝ]) {v : ℍ[ℝ]} (hv : v.re = 0) : (rotate q v).re = 0 := by
  rw [re_rotate, hv, mul_zero]

/-- The sandwich map scales the squared norm by $|q|^4$. -/
theorem normSq_rotate (q v : ℍ[ℝ]) : normSq (rotate q v) = normSq q ^ 2 * normSq v := by
  simp only [rotate, map_mul, normSq_star]
  ring

private theorem normSq_eq_one {q : ℍ[ℝ]} (hq : ‖q‖ = 1) : normSq q = 1 := by
  rw [normSq_eq_norm_mul_self, hq, mul_one]

/-- A unit quaternion's sandwich map is norm-preserving. -/
theorem norm_rotate {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (v : ℍ[ℝ]) :
    ‖rotate q v‖ = ‖v‖ := by
  simp only [rotate, norm_mul, norm_star, hq, one_mul, mul_one]

/-- Composition homomorphism: $\operatorname{rot}_{q_1 q_2} = \operatorname{rot}_{q_1} \circ
\operatorname{rot}_{q_2}$. -/
theorem rotate_mul (q₁ q₂ : ℍ[ℝ]) : rotate (q₁ * q₂) = rotate q₁ ∘ rotate q₂ := by
  funext v
  simp only [rotate, Function.comp_apply, star_mul, mul_assoc]

/-- Double cover: $q$ and $-q$ induce the same rotation. -/
theorem rotate_neg (q : ℍ[ℝ]) : rotate (-q) = rotate q := by
  funext v
  simp only [rotate, star_neg, neg_mul, mul_neg, neg_neg]

/-- The standard rotation matrix of a quaternion $q = w + xi + yj + zk$. -/
def rotMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := q.re; let x := q.imI; let y := q.imJ; let z := q.imK
  !![1 - 2 * (y ^ 2 + z ^ 2), 2 * (x * y - w * z), 2 * (x * z + w * y);
     2 * (x * y + w * z), 1 - 2 * (x ^ 2 + z ^ 2), 2 * (y * z - w * x);
     2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x ^ 2 + y ^ 2)]

/-- Homogeneous form of the rotation matrix, valid without the unit constraint. -/
private def homMatrix (q : ℍ[ℝ]) : Matrix (Fin 3) (Fin 3) ℝ :=
  let w := q.re; let x := q.imI; let y := q.imJ; let z := q.imK
  !![w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2, 2 * (x * y - w * z), 2 * (x * z + w * y);
     2 * (x * y + w * z), w ^ 2 - x ^ 2 + y ^ 2 - z ^ 2, 2 * (y * z - w * x);
     2 * (x * z - w * y), 2 * (y * z + w * x), w ^ 2 - x ^ 2 - y ^ 2 + z ^ 2]

private theorem rotMatrix_eq_homMatrix {q : ℍ[ℝ]} (hq : ‖q‖ = 1) :
    rotMatrix q = homMatrix q := by
  have h := normSq_eq_one hq
  rw [normSq_def'] at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMatrix, homMatrix] <;> linear_combination -h

private theorem homMatrix_transpose_mul_self (q : ℍ[ℝ]) :
    (homMatrix q)ᵀ * homMatrix q = normSq q ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homMatrix, Matrix.mul_apply, Fin.sum_univ_three, normSq_def'] <;> ring

private theorem homMatrix_mul_transpose_self (q : ℍ[ℝ]) :
    homMatrix q * (homMatrix q)ᵀ = normSq q ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [homMatrix, Matrix.mul_apply, Fin.sum_univ_three, normSq_def'] <;> ring

private theorem det_homMatrix (q : ℍ[ℝ]) : (homMatrix q).det = normSq q ^ 3 := by
  simp [homMatrix, Matrix.det_fin_three, normSq_def']
  ring

/-- Orthogonality of the quaternion rotation matrix: $R(q)^\top R(q) = I_3$ for $\|q\| = 1$. -/
theorem rotMatrix_transpose_mul_self {q : ℍ[ℝ]} (hq : ‖q‖ = 1) :
    (rotMatrix q)ᵀ * rotMatrix q = 1 := by
  rw [rotMatrix_eq_homMatrix hq, homMatrix_transpose_mul_self, normSq_eq_one hq]
  simp

/-- Orthogonality of the quaternion rotation matrix: $R(q) R(q)^\top = I_3$ for $\|q\| = 1$. -/
theorem rotMatrix_mul_transpose_self {q : ℍ[ℝ]} (hq : ‖q‖ = 1) :
    rotMatrix q * (rotMatrix q)ᵀ = 1 := by
  rw [rotMatrix_eq_homMatrix hq, homMatrix_mul_transpose_self, normSq_eq_one hq]
  simp

/-- Proper rotation: $\det R(q) = 1$ for $\|q\| = 1$. -/
theorem det_rotMatrix {q : ℍ[ℝ]} (hq : ‖q‖ = 1) : (rotMatrix q).det = 1 := by
  rw [rotMatrix_eq_homMatrix hq, det_homMatrix, normSq_eq_one hq, one_pow]

/-- $R(q)$ is a special orthogonal matrix for unit $q$. -/
theorem rotMatrix_mem_specialOrthogonalGroup {q : ℍ[ℝ]} (hq : ‖q‖ = 1) :
    rotMatrix q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using rotMatrix_mul_transpose_self hq,
    det_rotMatrix hq⟩

/-- The homogeneous matrix acts as the sandwich map on imaginary parts. -/
private theorem homMatrix_mulVec_imVec (q v : ℍ[ℝ]) :
    homMatrix q *ᵥ imVec v = imVec (rotate q v) := by
  ext i
  fin_cases i <;>
    simp [homMatrix, imVec, rotate, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- $R(q)$ acts as the sandwich map on imaginary parts:
$R(q)\,\operatorname{im}(v) = \operatorname{im}(q v \bar q)$ for $\|q\| = 1$. -/
theorem rotMatrix_mulVec_imVec {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (v : ℍ[ℝ]) :
    rotMatrix q *ᵥ imVec v = imVec (rotate q v) := by
  rw [rotMatrix_eq_homMatrix hq, homMatrix_mulVec_imVec]

/-- **Quaternion kinematics preserve the norm**: if $\dot q = \tfrac12 q \omega$ with $\omega$
pure (zero real part), then $\tfrac{d}{dt} |q(t)|^2 = 0$. -/
theorem hasDerivAt_normSq_kinematics {q ω : ℝ → ℍ[ℝ]} {t : ℝ} (hω : (ω t).re = 0)
    (hq : HasDerivAt q ((1 / 2 : ℝ) • (q t * ω t)) t) :
    HasDerivAt (fun s => normSq (q s)) 0 t := by
  have h := hq.norm_sq
  have hfun : (fun s => normSq (q s)) = (‖q ·‖ ^ 2) := by
    funext s; rw [normSq_eq_norm_mul_self, sq]
  rw [hfun]
  convert h using 1
  rw [inner_smul_right, inner_def, star_mul, ← mul_assoc, ← mul_assoc]
  have := rotate_re_eq_zero (q t) (v := star (ω t)) (by simpa using hω)
  simp only [rotate] at this
  rw [this]
  ring

end ControlsLean.Robotics
