import Mathlib
set_option maxHeartbeats 400000
namespace Factory
def statement : Prop :=
  ∀ (x : ℕ → ℝ) (ρ ε L : ℝ), 0 ≤ ρ →
    ε ≤ (1 - ρ) * L →
    (∀ n, x (n + 1) ≤ ρ * x n + ε) →
    ∀ n, x n ≤ ρ^n * (x 0 - L) + L
theorem solution : statement := by
  unfold statement
  intro x ρ ε L hρ hε hstep n
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih hρ
    have hs := hstep n
    rw [pow_succ]
    nlinarith
example : statement := solution
#print axioms solution
end Factory
