import HandoffAssembly
noncomputable section
set_option autoImplicit false
namespace S02Nonanticipation
open LeanControls LeanControls.DigitalHold LeanControls.ConstructiveHold

/-- Exact source recursion ignores every later rate, target-error and sensor
choice. This does not itself construct a state-dependent policy's arrays. -/
theorem finite_data_prefix (m : State) (g : ℝ → State)
    (R δ R' δ' : ℕ → ℝ) (ε ε' : ℕ → State) (n : ℕ)
    (hr : ∀ j, 1≤j → j≤n → R j=R' j)
    (hd : ∀ j, 1≤j → j≤n → δ j=δ' j)
    (he : ∀ j, j<n → ε j=ε' j) :
    state m g R δ ε n=state m g R' δ' ε' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun j hj hjn => hr j hj (by omega))
      (fun j hj hjn => hd j hj (by omega)) (fun j hj => he j (by omega))
    have hR := hr (n+1) (by omega) le_rfl
    have hD := hd (n+1) (by omega) le_rfl
    have hE := he n (by omega)
    simp only [state,hp]
    congr 1
    funext t
    simp only [phase,cellCommand,ConstructiveHold.measure,hR,hD,hE]

#print axioms finite_data_prefix
end S02Nonanticipation
