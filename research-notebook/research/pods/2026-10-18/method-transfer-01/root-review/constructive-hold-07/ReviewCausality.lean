import ConstructiveWitness
set_option maxHeartbeats 3000000
namespace ReviewCausality
open LeanControls.DigitalHold LeanControls.ConstructiveHold

/-- Changing future rate, target error or sensor error cannot change the
finite state already constructed. This inspects dependency, not hardware. -/
theorem finite_history (m : State) (g : ℝ → State)
    (R R' δ δ' : ℕ → ℝ) (ε ε' : ℕ → State) (N : ℕ) :
    (∀ k, 1 ≤ k → k ≤ N → R k=R' k) →
    (∀ k, 1 ≤ k → k ≤ N → δ k=δ' k) →
    (∀ k, k < N → ε k=ε' k) →
    state m g R δ ε N=state m g R' δ' ε' N := by
  induction N with
  | zero => intro hR hd he; rfl
  | succ n ih =>
    intro hR hd he
    have hp := ih (fun k hk hkn => hR k hk (by omega))
      (fun k hk hkn => hd k hk (by omega))
      (fun k hkn => he k (by omega))
    have hr := hR (n+1) (by omega) (by omega)
    have hdv := hd (n+1) (by omega) (by omega)
    have hev := he n (by omega)
    simp only [state, hp]
    congr 1
    funext t
    simp only [phase, cellCommand, LeanControls.ConstructiveHold.measure, hr, hdv, hev]

end ReviewCausality
#print axioms ReviewCausality.finite_history
