/-
Copyright (c) 2026 Mike Helsel. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Mike Helsel
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Monic
import ControlsLean.Controls.Reachability

/-!
# Companion matrices and pole placement in controllable canonical form

Part 1 of general-`n` single-input pole placement (issue #8).

For `a : Fin n → R` over a commutative ring, `companion a` is the `n × n` matrix in
**controllable canonical form**: ones on the superdiagonal, last row `-a`, zeros elsewhere.
$$\mathrm{companion}\ a = \begin{bmatrix}
  0 & 1 & & \\ & \ddots & \ddots & \\ & & 0 & 1 \\ -a_0 & -a_1 & \cdots & -a_{n-1}
\end{bmatrix}$$
The companion input vector is `companionB n = e_n = Pi.single (Fin.last n) 1`.

### Main results
* `charpoly_companion`: `charpoly (companion a) = X^n + ∑ i, C (a i) * X^i`, by Laplace
  expansion along the first column (`Matrix.det_succ_column_zero`).
* `companion_add_vecMulVec`: `companion a + b kᵀ = companion (a + k)`, so feedback
  `u = kᵀ x` only shifts the last row.
* `charpoly_companion_feedback`: with `k = a - d` the closed loop has characteristic
  polynomial `X^{n+1} + ∑ C (d i) X^i`.
* `exists_feedback_charpoly_eq`: every monic polynomial of degree `n + 1` is the closed-loop
  characteristic polynomial for some gain `k`.
* `controllable_companion`: over a field, the companion pair `(companion a, e_n)` is
  controllable in the sense of `ControlsLean.Controls.Controllable`.

The change of basis bringing an arbitrary controllable `(A, b)` into this form, and the
general pole placement theorem, are in `ControlsLean.Controls.PolePlacementGeneral`.
-/

open Matrix Polynomial

namespace ControlsLean.Controls

section CommRing

variable {R : Type*} [CommRing R]

/-- Companion matrix in controllable canonical form: superdiagonal of ones, last row `-a`. -/
def companion {n : ℕ} (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) + 1 = n then -a j else if (j : ℕ) = i + 1 then 1 else 0

theorem companion_apply {n : ℕ} (a : Fin n → R) (i j : Fin n) :
    companion a i j = if (i : ℕ) + 1 = n then -a j else if (j : ℕ) = i + 1 then 1 else 0 :=
  rfl

/-- Deleting the first row and column of `X·I - companion a` leaves the characteristic
matrix of the companion matrix of the tail coefficients. -/
private theorem charmatrix_companion_submatrix_succ {n : ℕ} (a : Fin (n + 2) → R) :
    (charmatrix (companion a)).submatrix Fin.succ Fin.succ =
      charmatrix (companion fun j : Fin (n + 1) => a j.succ) := by
  ext i j
  simp only [submatrix_apply, charmatrix_apply, diagonal_apply, Fin.succ_inj, companion_apply,
    Fin.val_succ]
  congr 2
  split_ifs <;> first | rfl | omega

/-- Deleting the last row and first column of `X·I - companion a` leaves a lower-triangular
matrix with `-1` on the diagonal. -/
private theorem det_charmatrix_companion_submatrix_last {n : ℕ} (a : Fin (n + 2) → R) :
    ((charmatrix (companion a)).submatrix (Fin.last (n + 1)).succAbove Fin.succ).det =
      (-1) ^ (n + 1) := by
  rw [Fin.succAbove_last, det_of_isLowerTriangular]
  · have h : ∀ i : Fin (n + 1), charmatrix (companion a) i.castSucc i.succ = -1 := by
      intro i
      have hne : (Fin.castSucc i : Fin (n + 2)) ≠ i.succ := Fin.castSucc_lt_succ.ne
      have hi : (i : ℕ) ≠ n + 1 := by omega
      rw [charmatrix_apply_ne _ _ _ hne, companion_apply]
      simp [hi]
    simp only [submatrix_apply, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have h1 : (i : ℕ) ≠ j + 1 := by omega
    have h2 : (i : ℕ) ≠ n + 1 := by omega
    have h3 : (j : ℕ) ≠ i := by omega
    simp [companion_apply, Fin.ext_iff, h1, h2, h3]

/-- **Characteristic polynomial of the companion matrix**:
`det (X·I - companion a) = X^n + a_{n-1} X^{n-1} + ⋯ + a_1 X + a_0`. -/
theorem charpoly_companion : ∀ {n : ℕ} (a : Fin n → R),
    (companion a).charpoly = X ^ n + ∑ i, C (a i) * X ^ (i : ℕ)
  | 0, a => by simp [Matrix.charpoly]
  | 1, a => by
    rw [Matrix.charpoly, det_unique]
    simp [companion_apply]
  | n + 2, a => by
    rw [Matrix.charpoly, det_succ_column_zero, Fin.sum_univ_succ,
      Finset.sum_eq_single (Fin.last n)]
    · rw [Fin.succAbove_zero, Fin.succ_last, charmatrix_companion_submatrix_succ,
        ← Matrix.charpoly, charpoly_companion, det_charmatrix_companion_submatrix_last]
      have h00 : charmatrix (companion a) 0 0 = X := by
        rw [charmatrix_apply_eq, companion_apply]; simp
      have hl0 : charmatrix (companion a) (Fin.last (n + 1)) 0 = C (a 0) := by
        rw [charmatrix_apply_ne _ _ _ (Fin.last_pos.ne'), companion_apply]; simp
      rw [h00, hl0, Fin.sum_univ_succ (n := n + 1)]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, Fin.val_last, mul_one]
      rw [mul_add, Finset.mul_sum]
      have hs : ((-1 : R[X]) ^ (n + 1) * C (a 0) * (-1) ^ (n + 1)) = C (a 0) := by
        rw [mul_comm, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
      rw [hs]
      simp only [pow_succ]
      ring_nf
    · intro i _ hi
      have hi' : (i : ℕ) ≠ n := fun h => hi (Fin.ext h)
      rw [charmatrix_apply_ne _ _ _ (Fin.succ_ne_zero _), companion_apply]
      simp [hi']
    · simp

/-! ### Companion input vector and state feedback -/

/-- Input vector of the controllable canonical form: `e_n = (0, …, 0, 1)`. -/
def companionB (n : ℕ) : Fin (n + 1) → R := Pi.single (Fin.last n) 1

/-- **Feedback shifts the last row**: `companion a + b kᵀ = companion (a - k)`. -/
theorem companion_add_vecMulVec {n : ℕ} (a k : Fin (n + 1) → R) :
    companion a + vecMulVec (companionB n) k = companion (a - k) := by
  ext i j
  simp only [Matrix.add_apply, vecMulVec_apply, companionB, companion_apply, Pi.single_apply,
    Pi.sub_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | omega | ring

/-- **Closed-loop characteristic polynomial**: choosing `k = a - d` assigns the closed-loop
characteristic polynomial `X^{n+1} + ∑ C (d i) X^i`. -/
theorem charpoly_companion_feedback {n : ℕ} (a d : Fin (n + 1) → R) :
    (companion a + vecMulVec (companionB n) (a - d)).charpoly =
      X ^ (n + 1) + ∑ i, C (d i) * X ^ (i : ℕ) := by
  rw [companion_add_vecMulVec, sub_sub_cancel, charpoly_companion]

/-- **Pole placement in controllable canonical form**: every monic polynomial of degree
`n + 1` is the characteristic polynomial of `companion a + b kᵀ` for some gain `k`. -/
theorem exists_feedback_charpoly_eq {n : ℕ} (a : Fin (n + 1) → R) {p : R[X]} (hp : p.Monic)
    (hdeg : p.natDegree = n + 1) :
    ∃ k : Fin (n + 1) → R, (companion a + vecMulVec (companionB n) k).charpoly = p := by
  refine ⟨a - fun i : Fin (n + 1) => p.coeff i, ?_⟩
  rw [charpoly_companion_feedback]
  conv_rhs => rw [hp.as_sum, hdeg, ← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]

end CommRing

/-! ### Controllability of the companion pair -/

section Field

variable {K : Type*} [Field K]

/-- The linear functional `x ↦ k ⬝ᵥ x`. -/
private def dotL {n : ℕ} (k : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun x := k ⬝ᵥ x
  map_add' := dotProduct_add k
  map_smul' c x := dotProduct_smul c k x

private theorem toLin'_add_vecMulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b k : Fin n → K) :
    toLin' (A + vecMulVec b k) = toLin' A + LinearMap.toSpanSingleton K _ b ∘ₗ dotL k := by
  refine LinearMap.ext fun x => ?_
  simp [dotL, vecMulVec_mulVec]

/-- The shift `companion 0` sends `e_{j+1}` to `e_j`. -/
private theorem companion_zero_mulVec_single {n : ℕ} (j : Fin n) :
    companion (0 : Fin (n + 1) → K) *ᵥ Pi.single j.succ 1 = Pi.single j.castSucc 1 := by
  ext i
  simp only [mulVec_single_one, col_apply, companion_apply, Pi.zero_apply, neg_zero,
    Pi.single_apply, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
  have := i.isLt
  have := j.isLt
  split_ifs <;> first | rfl | omega

/-- `e_j` is reachable through the shift in `n - j + 1` steps. -/
private theorem single_mem_reach_shift {n : ℕ} :
    ∀ (m : ℕ) (j : Fin (n + 1)), (j : ℕ) + m = n →
      Pi.single j (1 : K) ∈
        reach (toLin' (companion (0 : Fin (n + 1) → K)))
          (LinearMap.toSpanSingleton K _ (companionB n)) (m + 1)
  | 0, j, hj => by
    have : j = Fin.last n := Fin.ext (by simpa using hj)
    subst this
    rw [reach_succ]
    exact Submodule.mem_sup_left ⟨1, by simp [companionB]⟩
  | m + 1, j, hj => by
    let jn : Fin n := ⟨j, by omega⟩
    have ih := single_mem_reach_shift m jn.succ (by simp [jn]; omega)
    have hj' : jn.castSucc = j := Fin.ext rfl
    rw [reach_succ]
    refine Submodule.mem_sup_right ⟨_, ih, ?_⟩
    rw [toLin'_apply, companion_zero_mulVec_single, hj']

/-- **Companion pairs are controllable**: `(companion a, e_n)` satisfies `Controllable`. -/
theorem controllable_companion {n : ℕ} (a : Fin (n + 1) → K) :
    Controllable (toLin' (companion a)) (LinearMap.toSpanSingleton K _ (companionB n)) := by
  have hshift : toLin' (companion (0 : Fin (n + 1) → K)) =
      toLin' (companion a) + LinearMap.toSpanSingleton K _ (companionB n) ∘ₗ dotL a := by
    rw [← toLin'_add_vecMulVec, companion_add_vecMulVec, sub_self]
  rw [← controllable_feedback (dotL a), ← hshift, Controllable, Module.finrank_fin_fun]
  refine eq_top_iff.2 fun x _ => ?_
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  have hlt := j.isLt
  have hs : (fun j' => if j = j' then (1 : K) else 0) = Pi.single j 1 := by
    ext j'; simp [Pi.single_apply, eq_comm]
  rw [hs]
  exact reach_mono (show n - j + 1 ≤ n + 1 by omega)
    (single_mem_reach_shift (K := K) (n - j) j (by omega))

/-- Feedback preserves controllability of the companion pair. -/
theorem controllable_companion_feedback {n : ℕ} (a k : Fin (n + 1) → K) :
    Controllable (toLin' (companion a + vecMulVec (companionB n) k))
      (LinearMap.toSpanSingleton K _ (companionB n)) := by
  rw [companion_add_vecMulVec]
  exact controllable_companion _

end Field

end ControlsLean.Controls
