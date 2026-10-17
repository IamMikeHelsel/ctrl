/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import ControlsLean.Vision.Epipolar
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The eight-point algorithm: the essential matrix is determined up to scale

Each correspondence `(x₁, x₂)` gives one linear equation `x₂ᵀ E x₁ = 0` in the nine entries of
`E`. Stacking `n` of them gives the constraint matrix
`M : Matrix (Fin n) (Fin 3 × Fin 3) K` with `M i (a, b) = x₂ᵢ a * x₁ᵢ b`, so that the
constraints read `M *ᵥ vec E = 0`. If `rank M = 8` (the generic situation for `n = 8`
correspondences), rank–nullity gives a one-dimensional kernel, so all solutions are proportional.
Since the true essential matrix `[t]ₓ R` satisfies every constraint, any nonzero solution is a
scalar multiple of it.

This is only the exact linear-algebra core of the algorithm: there is no noise model, no
least-squares/SVD step, and no projection onto rank-2 matrices.
-/

open Matrix Module

namespace ControlsLean.Vision

variable {K : Type*} [Field K] {n : ℕ}

/-- Row-major vectorisation of a `3 × 3` matrix, indexed by `Fin 3 × Fin 3`. -/
def vec3 (E : Matrix (Fin 3) (Fin 3) K) : Fin 3 × Fin 3 → K := fun p => E p.1 p.2

omit [Field K] in
theorem vec3_injective : Function.Injective (vec3 (K := K)) := fun E E' h => by
  ext a b; exact congrFun h (a, b)

@[simp] theorem vec3_smul (c : K) (E : Matrix (Fin 3) (Fin 3) K) : vec3 (c • E) = c • vec3 E :=
  rfl

theorem vec3_ne_zero {E : Matrix (Fin 3) (Fin 3) K} (hE : E ≠ 0) : vec3 E ≠ 0 := fun h =>
  hE (vec3_injective (by rw [h]; rfl))

/-- The eight-point constraint matrix: row `i` is `x₂ᵢ ⊗ x₁ᵢ`. -/
def constraintMatrix (x₁ x₂ : Fin n → Fin 3 → K) : Matrix (Fin n) (Fin 3 × Fin 3) K :=
  of fun i p => x₂ i p.1 * x₁ i p.2

/-- Row `i` of `M *ᵥ vec E` is the epipolar residual `x₂ᵢᵀ E x₁ᵢ`. -/
theorem constraintMatrix_mulVec_apply (x₁ x₂ : Fin n → Fin 3 → K)
    (E : Matrix (Fin 3) (Fin 3) K) (i : Fin n) :
    (constraintMatrix x₁ x₂ *ᵥ vec3 E) i = x₂ i ⬝ᵥ (E *ᵥ x₁ i) := by
  simp only [mulVec, dotProduct, constraintMatrix, vec3, of_apply, Fintype.sum_prod_type,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- `E` satisfies all epipolar constraints iff `vec E` lies in the kernel of `M`. -/
theorem mem_ker_constraintMatrix_iff (x₁ x₂ : Fin n → Fin 3 → K)
    (E : Matrix (Fin 3) (Fin 3) K) :
    vec3 E ∈ LinearMap.ker (constraintMatrix x₁ x₂).mulVecLin ↔
      ∀ i, x₂ i ⬝ᵥ (E *ᵥ x₁ i) = 0 := by
  rw [LinearMap.mem_ker, mulVecLin_apply, funext_iff]
  simp [constraintMatrix_mulVec_apply]

/-- **Rank–nullity.** If the constraint matrix has rank 8, its kernel is one-dimensional. -/
theorem finrank_ker_constraintMatrix {x₁ x₂ : Fin n → Fin 3 → K}
    (hrank : (constraintMatrix x₁ x₂).rank = 8) :
    finrank K (LinearMap.ker (constraintMatrix x₁ x₂).mulVecLin) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (constraintMatrix x₁ x₂).mulVecLin
  rw [← Matrix.rank, hrank, finrank_fintype_fun_eq_card] at h
  simp at h
  omega

/-- **Eight-point uniqueness.** If the constraint matrix has rank 8 and `E ≠ 0` satisfies all
the epipolar constraints, then every solution `E'` is a scalar multiple of `E`. -/
theorem eq_smul_of_rank_eq_eight {x₁ x₂ : Fin n → Fin 3 → K}
    (hrank : (constraintMatrix x₁ x₂).rank = 8) {E E' : Matrix (Fin 3) (Fin 3) K}
    (hE0 : E ≠ 0) (hE : ∀ i, x₂ i ⬝ᵥ (E *ᵥ x₁ i) = 0) (hE' : ∀ i, x₂ i ⬝ᵥ (E' *ᵥ x₁ i) = 0) :
    ∃ c : K, E' = c • E := by
  set S := LinearMap.ker (constraintMatrix x₁ x₂).mulVecLin
  let v : S := ⟨vec3 E, (mem_ker_constraintMatrix_iff x₁ x₂ E).2 hE⟩
  let w : S := ⟨vec3 E', (mem_ker_constraintMatrix_iff x₁ x₂ E').2 hE'⟩
  have hv : v ≠ 0 := fun h => vec3_ne_zero hE0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (finrank_ker_constraintMatrix hrank) hv w
  refine ⟨c, vec3_injective ?_⟩
  rw [vec3_smul]
  exact (congrArg Subtype.val hc).symm

/-- The true essential matrix lies in the kernel: it satisfies the constraint of every
correspondence that comes from a scene point with nonzero depth in camera 2. -/
theorem essential_satisfies_constraints (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K)
    {x₁ x₂ : Fin n → Fin 3 → K} {d₁ d₂ : Fin n → K} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t) :
    ∀ i, x₂ i ⬝ᵥ (essential R t *ᵥ x₁ i) = 0 := fun i =>
  epipolar_constraint R t (x₁ i) (x₂ i) (d₁ i) (d₂ i) (hd₂ i) (hscene i)

theorem vec3_essential_mem_ker (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K)
    {x₁ x₂ : Fin n → Fin 3 → K} {d₁ d₂ : Fin n → K} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t) :
    vec3 (essential R t) ∈ LinearMap.ker (constraintMatrix x₁ x₂).mulVecLin :=
  (mem_ker_constraintMatrix_iff x₁ x₂ _).2 (essential_satisfies_constraints R t hd₂ hscene)

/-- **Eight-point algorithm, recovery up to scale.** For correspondences generated by a rigid
motion `(R, t)` whose constraint matrix has rank 8, any nonzero `E` satisfying all the epipolar
constraints is a nonzero scalar multiple of the true essential matrix `[t]ₓ R`, provided the
latter is nonzero. -/
theorem eq_smul_essential (R : Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K)
    {x₁ x₂ : Fin n → Fin 3 → K} {d₁ d₂ : Fin n → K} (hd₂ : ∀ i, d₂ i ≠ 0)
    (hscene : ∀ i, d₂ i • x₂ i = R *ᵥ (d₁ i • x₁ i) + t)
    (hrank : (constraintMatrix x₁ x₂).rank = 8) (hess : essential R t ≠ 0)
    {E : Matrix (Fin 3) (Fin 3) K} (hE0 : E ≠ 0) (hE : ∀ i, x₂ i ⬝ᵥ (E *ᵥ x₁ i) = 0) :
    ∃ c : K, c ≠ 0 ∧ E = c • essential R t := by
  obtain ⟨c, rfl⟩ :=
    eq_smul_of_rank_eq_eight hrank hess (essential_satisfies_constraints R t hd₂ hscene) hE
  exact ⟨c, fun hc => hE0 (by simp [hc]), rfl⟩

end ControlsLean.Vision
