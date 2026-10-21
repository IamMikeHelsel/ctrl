import Mathlib

/- AI-written exact witness for a limitation of a proposed MF13 search reduction.
   This does not settle the dimension-six Lyapunov norm question.
   K and Y have equal norm but are not unit normalized in this file. -/

namespace Crossover60.M05

noncomputable section

abbrev K : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0;
    0, 0, -2, 0, 0, 0;
    0, 0, 0, 0, 0, 1/2;
    0, 0, 0, 0, -1/2, 0]

abbrev Y : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 1, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0;
    0, 0, 0, 1/2, 0, 0;
    0, 0, -1/2, 0, 0, 0;
    0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, -2, 0]

theorem product_identity : K * Y = -1 ∧ Y * K = -1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [K, Y, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem skew_and_equal_energy :
    K.transpose = -K ∧ Y.transpose = -Y ∧
    Matrix.trace (K * K) = Matrix.trace (Y * Y) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [K, Matrix.transpose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Y, Matrix.transpose_apply]
  · norm_num [K, Y, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

theorem no_coupled_solution :
    ¬ ∃ A : Matrix (Fin 6) (Fin 6) ℝ,
      A * K + K * A.transpose = Y ∧ A.transpose * Y + Y * A = K := by
  rintro ⟨A, h₁, h₂⟩
  have e₁ := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 2 3) h₁
  have e₂ := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 2 3) h₂
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] at e₁ e₂
  norm_num [Fin.sum_univ_succ, K, Y, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail] at e₁ e₂
  change A 2 2 * 2 + 2 * A 3 3 = (1 : ℝ) / 2 at e₁
  change A 2 2 * (1 / 2) + (1 / 2) * A 3 3 = 2 at e₂
  linarith

theorem reduced_map_zero (H : Matrix (Fin 6) (Fin 6) ℝ) :
    (K * Y) * H - H * (Y * K) = 0 := by
  rw [product_identity.1, product_identity.2]
  simp

theorem all_moments_zero (j : ℕ) :
    Matrix.trace ((Y * K) ^ j * (Y * Y - K * K)) = 0 := by
  induction j with
  | zero =>
    simpa only [pow_zero, one_mul, Matrix.trace_sub, sub_eq_zero] using
      skew_and_equal_energy.2.2.symm
  | succ j ih =>
    rw [pow_succ, product_identity.2]
    simpa only [product_identity.2, mul_neg, mul_one, neg_mul, Matrix.trace_neg,
      neg_eq_zero] using ih

#print axioms product_identity
#print axioms skew_and_equal_energy
#print axioms no_coupled_solution
#print axioms reduced_map_zero
#print axioms all_moments_zero

end
end Crossover60.M05
