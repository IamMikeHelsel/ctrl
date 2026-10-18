module
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

/-! An elementary structured case of the symmetric-maximizer question.
This is a learning baseline, not a new resolution of the open order-six case.
-/
@[expose] public section
noncomputable section
namespace LeanControls.DiagonalLyapunov
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def frobeniusSquared (X : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, X i j ^ 2
def action (a : n → ℝ) (X : Matrix n n ℝ) : Matrix n n ℝ :=
  diagonal a * X + X * (diagonal a).transpose

theorem action_entry (a : n → ℝ) (X : Matrix n n ℝ) (i j : n) :
    action a X i j = (a i + a j) * X i j := by
  simp [action, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem norm_bound (a : n → ℝ) (X : Matrix n n ℝ) {M : ℝ}
    (ha : ∀ i, |a i| ≤ M) :
    frobeniusSquared (action a X) ≤ 4 * M ^ 2 * frobeniusSquared X := by
  unfold frobeniusSquared
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [action_entry]
  have hi := abs_le.mp (ha i)
  have hj := abs_le.mp (ha j)
  have hs : (a i + a j) ^ 2 ≤ 4 * M ^ 2 := by nlinarith [hi.1, hi.2, hj.1, hj.2]
  have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (X i j))
  nlinarith only [hp]

def witness (k : n) : Matrix n n ℝ := fun i j => if i = k then (if j = k then 1 else 0) else 0

omit [Fintype n] in
theorem witness_symmetric (k : n) : (witness k).transpose = witness k := by
  ext i j
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp [Matrix.transpose_apply, witness, hi, hj]

theorem witness_unit (k : n) : frobeniusSquared (witness k) = 1 := by
  simp [frobeniusSquared, witness]

theorem witness_attains (a : n → ℝ) (k : n) :
    frobeniusSquared (action a (witness k)) = 4 * (a k) ^ 2 := by
  simp [frobeniusSquared, action_entry, witness]
  ring

/-- A symmetric unit witness dominates all unit matrices when a maximal entry is given. -/
theorem symmetric_maximizer (a : n → ℝ) (k : n)
    (hk : ∀ i, |a i| ≤ |a k|) :
    ∃ S : Matrix n n ℝ, S.transpose = S ∧ frobeniusSquared S = 1 ∧
      ∀ X : Matrix n n ℝ, frobeniusSquared X = 1 →
        frobeniusSquared (action a X) ≤ frobeniusSquared (action a S) := by
  refine ⟨witness k, witness_symmetric k, witness_unit k, ?_⟩
  intro X hX
  have hb := norm_bound a X hk
  rw [hX, mul_one, sq_abs] at hb
  rw [witness_attains]
  exact hb

end LeanControls.DiagonalLyapunov
