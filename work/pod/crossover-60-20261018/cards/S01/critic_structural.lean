import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace S01Critic
-- Synthetic infinitely-branching countdown-tree obstruction, not the C7 recurrence.
theorem no_infinite_countdown : ¬ ∃ f : ℕ → ℕ, ∀ n, f (n+1)<f n := by
  rintro ⟨f,hf⟩
  have bound : ∀ n, f n+n ≤ f 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have hn := hf n; omega
  have impossible := bound (f 0+1)
  omega
-- Same local physical state and allowed sensor box, but distinct outgoing commands.
theorem distinct_accel_reading_commands :
    |(1:ℝ)/20|≤1/20 ∧ |-(1:ℝ)/20|≤1/20 ∧
    -((1:ℝ)/20)/2 = -1/40 ∧ -(-(1:ℝ)/20)/2 = 1/40 ∧
    (8:ℝ)*(-1/40) ≠ 8*(1/40) := by norm_num
-- Variable latency in the SAME [0,h] band permits a tie, so strict order needs more.
theorem variable_latency_tie :
    (0:ℝ)<1/2000 ∧ (0:ℝ)+1/2000=1/2000+0 := by norm_num
#print axioms no_infinite_countdown
#print axioms distinct_accel_reading_commands
#print axioms variable_latency_tie
end S01Critic
