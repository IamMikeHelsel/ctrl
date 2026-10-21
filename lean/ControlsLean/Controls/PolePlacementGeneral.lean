/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.Polynomial.Inductions
import ControlsLean.Controls.Companion

/-!
# Pole placement for single-input controllable systems (general `n`)

Closes issue #8. Let `K` be a field, `A : Matrix (Fin (n+1)) (Fin (n+1)) K` and
`b : Fin (n+1) → K` with `(A, b)` controllable. Then every monic polynomial `p` of degree
`n + 1` is the characteristic polynomial of the closed loop `A + b kᵀ` for some gain `k`.

### Proof
Write `χ = charpoly A = X^{n+1} + c_n X^n + ⋯ + c_0` and `q_j = divX^[j+1] χ`, so that
`q_n = 1` and `X q_j + c_j = q_{j-1}` (with `q_{-1} = χ`). The vectors `w_j = q_j(A) b`
therefore satisfy the Horner recursion
$$w_n = b, \qquad A w_j = w_{j-1} - c_j b, \qquad A w_0 = -c_0 b,$$
the last identity by Cayley–Hamilton. Their span contains `b` and is `A`-invariant, so it
contains every reachable subspace; controllability makes it everything, and `n + 1`
spanning vectors in an `(n+1)`-dimensional space are a basis (`canonBasis`). In this basis
`A` is `companion c` and `b` is `e_n`, so `A + b kᵀ` becomes `companion c + e_n k'ᵀ` with
`k'_j = k ⬝ᵥ w_j`. The characteristic polynomial is basis-independent
(`LinearMap.charpoly_toMatrix`), and `exists_feedback_charpoly_eq` supplies `k'`; any `k'`
is realised by some `k` because the `w_j` are a basis.

### Main results
* `mulVec_canonVec_zero`, `mulVec_canonVec_succ`, `canonVec_last`: the Horner recursion.
* `top_le_span_canonVec`: for a controllable pair the vectors `w_j` span.
* `canonBasis`: the controllable-canonical-form basis.
* `toMatrix_canonBasis`: in `canonBasis`, `A` has matrix `companion c`
  (and `repr_canonBasis_b`: `b` has coordinates `e_n`).
* `toMatrix_canonBasis_add_vecMulVec`: the closed loop has matrix
  `companion c + e_n k'ᵀ`.
* `charpoly_add_vecMulVec_eq`: similarity transport of the closed-loop characteristic
  polynomial to canonical form.
* `pole_placement`: **pole placement theorem**.
-/

open Matrix Polynomial Module
open LinearMap (range)

namespace ControlsLean.Controls

section Poly

variable {R : Type*} [CommRing R]

theorem coeff_divX_iterate (p : R[X]) (m k : ℕ) : (divX^[m] p).coeff k = p.coeff (k + m) := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeff_divX, ih]
    congr 1
    omega

theorem divX_iterate_natDegree {p : R[X]} (hp : p.Monic) : divX^[p.natDegree] p = 1 := by
  ext k
  rw [coeff_divX_iterate, coeff_one]
  rcases k with _ | k
  · simpa using hp.coeff_natDegree
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- One Horner step: `X · divX^[m+1] p + p_m = divX^[m] p`. -/
theorem X_mul_divX_iterate_succ_add (p : R[X]) (m : ℕ) :
    X * divX^[m + 1] p + C (p.coeff m) = divX^[m] p := by
  have h := X_mul_divX_add (divX^[m] p)
  rwa [coeff_divX_iterate, zero_add, ← Function.iterate_succ_apply' divX] at h

end Poly

section Field

variable {K : Type*} [Field K] {n : ℕ}
variable (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (b : Fin (n + 1) → K)

/-- The controllable-canonical-form vectors `w_j = (divX^[j+1] (charpoly A))(A) b`. -/
noncomputable def canonVec (j : Fin (n + 1)) : Fin (n + 1) → K :=
  aeval A (divX^[(j : ℕ) + 1] A.charpoly) *ᵥ b

private theorem mulVec_aeval_divX_iterate (j : ℕ) :
    A *ᵥ (aeval A (divX^[j + 1] A.charpoly) *ᵥ b) =
      aeval A (divX^[j] A.charpoly) *ᵥ b - A.charpoly.coeff j • b := by
  rw [← X_mul_divX_iterate_succ_add A.charpoly j, map_add, map_mul, aeval_X, aeval_C,
    add_mulVec, mulVec_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec,
    add_sub_cancel_right]

/-- Cayley–Hamilton step of the Horner recursion: `A w_0 = -c_0 b`. -/
theorem mulVec_canonVec_zero : A *ᵥ canonVec A b 0 = -(A.charpoly.coeff 0 • b) := by
  rw [canonVec, Fin.val_zero, mulVec_aeval_divX_iterate, Function.iterate_zero_apply,
    aeval_self_charpoly, zero_mulVec, zero_sub]

/-- Horner recursion: `A w_{j+1} = w_j - c_{j+1} b`. -/
theorem mulVec_canonVec_succ (j : Fin n) :
    A *ᵥ canonVec A b j.succ =
      canonVec A b j.castSucc - A.charpoly.coeff (j + 1) • b := by
  rw [canonVec, Fin.val_succ, mulVec_aeval_divX_iterate]
  rfl

/-- `w_n = b`. -/
theorem canonVec_last : canonVec A b (Fin.last n) = b := by
  have h : A.charpoly.natDegree = n + 1 := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h1 := divX_iterate_natDegree (charpoly_monic A)
  rw [h] at h1
  rw [canonVec, Fin.val_last, h1, map_one, one_mulVec]

variable {A b}

/-- For a controllable pair the canonical-form vectors span the state space. -/
theorem top_le_span_canonVec
    (hc : Controllable (toLin' A) (LinearMap.toSpanSingleton K _ b)) :
    ⊤ ≤ Submodule.span K (Set.range (canonVec A b)) := by
  set S := Submodule.span K (Set.range (canonVec A b))
  have hb : b ∈ S := canonVec_last A b ▸ Submodule.subset_span ⟨_, rfl⟩
  have hA : ∀ x ∈ S, A *ᵥ x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      cases j using Fin.cases with
      | zero =>
        rw [mulVec_canonVec_zero]
        exact S.neg_mem (S.smul_mem _ hb)
      | succ j =>
        rw [mulVec_canonVec_succ]
        exact S.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (S.smul_mem _ hb)
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [mulVec_smul]; exact S.smul_mem a hx
  have hreach : ∀ k, reach (toLin' A) (LinearMap.toSpanSingleton K _ b) k ≤ S := by
    intro k
    induction k with
    | zero => exact bot_le
    | succ k ih =>
      rw [reach_succ]
      refine sup_le ?_ ?_
      · rintro _ ⟨t, rfl⟩
        rw [LinearMap.toSpanSingleton_apply]
        exact S.smul_mem t hb
      · rintro _ ⟨x, hx, rfl⟩
        rw [toLin'_apply]
        exact hA x (ih hx)
  exact hc ▸ hreach _

/-- The controllable-canonical-form basis `w_0, …, w_n` of a controllable pair. -/
noncomputable def canonBasis (hc : Controllable (toLin' A) (LinearMap.toSpanSingleton K _ b)) :
    Basis (Fin (n + 1)) K (Fin (n + 1) → K) :=
  basisOfTopLeSpanOfCardEqFinrank (canonVec A b) (top_le_span_canonVec hc) (by simp)

variable (hc : Controllable (toLin' A) (LinearMap.toSpanSingleton K _ b))

@[simp] theorem canonBasis_apply (j : Fin (n + 1)) : canonBasis hc j = canonVec A b j := by
  simp [canonBasis]

theorem repr_canonVec (j : Fin (n + 1)) :
    (canonBasis hc).repr (canonVec A b j) = Finsupp.single j 1 := by
  rw [← canonBasis_apply hc, Basis.repr_self]

/-- In the canonical basis, `b` has coordinates `e_n`. -/
theorem repr_canonBasis_b : (canonBasis hc).repr b = Finsupp.single (Fin.last n) 1 := by
  rw [← repr_canonVec hc, canonVec_last]

/-- **Controllable canonical form**: in `canonBasis`, `A` has matrix `companion c`, where
`c_i` are the coefficients of `charpoly A`. -/
theorem toMatrix_canonBasis :
    LinearMap.toMatrix (canonBasis hc) (canonBasis hc) (toLin' A) =
      companion fun i : Fin (n + 1) => A.charpoly.coeff i := by
  ext i j
  rw [LinearMap.toMatrix_apply, toLin'_apply, canonBasis_apply, companion_apply]
  cases j using Fin.cases with
  | zero =>
    rw [mulVec_canonVec_zero, map_neg, map_smul, repr_canonBasis_b]
    simp only [Finsupp.neg_apply, Finsupp.smul_apply, Finsupp.single_apply, Fin.ext_iff,
      Fin.val_last, Fin.val_zero, smul_eq_mul]
    split_ifs <;> first | omega | simp_all
  | succ j =>
    rw [mulVec_canonVec_succ, map_sub, map_smul, repr_canonBasis_b, repr_canonVec]
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply, Fin.ext_iff,
      Fin.val_last, Fin.val_succ, Fin.val_castSucc, smul_eq_mul]
    split_ifs <;> first | omega | simp_all

/-- In `canonBasis`, the closed loop `A + b kᵀ` has matrix `companion c + e_n k'ᵀ` with
`k'_j = k ⬝ᵥ w_j`. -/
theorem toMatrix_canonBasis_add_vecMulVec (k : Fin (n + 1) → K) :
    LinearMap.toMatrix (canonBasis hc) (canonBasis hc) (toLin' (A + vecMulVec b k)) =
      companion (fun i : Fin (n + 1) => A.charpoly.coeff i) +
        vecMulVec (companionB n) fun j => k ⬝ᵥ canonVec A b j := by
  ext i j
  rw [LinearMap.toMatrix_apply, toLin'_apply, add_mulVec, map_add, Finsupp.add_apply,
    ← toLin'_apply, ← LinearMap.toMatrix_apply, toMatrix_canonBasis, Matrix.add_apply,
    vecMulVec_mulVec, op_smul_eq_smul, map_smul, repr_canonBasis_b, canonBasis_apply]
  simp [vecMulVec_apply, companionB, Pi.single_apply, Finsupp.single_apply, eq_comm, mul_comm]

/-- **Similarity transport**: the closed-loop characteristic polynomial of a controllable
pair equals that of the companion form with the transformed gain `k'_j = k ⬝ᵥ w_j`. -/
theorem charpoly_add_vecMulVec_eq
    (hc : Controllable (toLin' A) (LinearMap.toSpanSingleton K _ b)) (k : Fin (n + 1) → K) :
    (A + vecMulVec b k).charpoly =
      (companion (fun i : Fin (n + 1) => A.charpoly.coeff i) +
        vecMulVec (companionB n) fun j => k ⬝ᵥ canonVec A b j).charpoly := by
  rw [← charpoly_toLin', ← LinearMap.charpoly_toMatrix _ (canonBasis hc),
    toMatrix_canonBasis_add_vecMulVec]

variable (A b) in
/-- **Pole placement theorem** (single input, any field): if `(A, b)` is controllable, every
monic polynomial of degree `n + 1` is the closed-loop characteristic polynomial
`charpoly (A + b kᵀ)` for some state-feedback gain `k`. -/
theorem pole_placement
    (hc : Controllable (toLin' A) (LinearMap.toSpanSingleton K _ b)) {p : K[X]} (hp : p.Monic)
    (hdeg : p.natDegree = n + 1) :
    ∃ k : Fin (n + 1) → K, (A + vecMulVec b k).charpoly = p := by
  obtain ⟨k', hk'⟩ := exists_feedback_charpoly_eq (fun i : Fin (n + 1) => A.charpoly.coeff i)
    hp hdeg
  set W := canonBasis hc
  set f : (Fin (n + 1) → K) →ₗ[K] K := W.constr K k'
  refine ⟨fun i => f fun j => if i = j then 1 else 0, ?_⟩
  have hk : (fun j => (fun i => f fun j => if i = j then 1 else 0) ⬝ᵥ canonVec A b j) = k' := by
    funext j
    rw [show k' j = f (W j) from (W.constr_basis K k' j).symm,
      LinearMap.pi_apply_eq_sum_univ f (W j), canonBasis_apply, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [charpoly_add_vecMulVec_eq hc, hk, hk']

end Field

end ControlsLean.Controls
