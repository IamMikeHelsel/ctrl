import Mathlib.Data.Set.Basic

/- AI-written generic logical contract for S12. No dynamic plant claim.
   This is an isolated research theorem, not an approved Challenge solution.
   Evidence containment and physical meaning of Safe remain hypotheses. -/
namespace S12Guarded

variable {World Branch : Type*}

def GuardedAcceptance (retained safe : World → Prop) : Prop :=
  (∃ w, retained w) ∧ ∀ w, retained w → safe w

theorem update_preserves_truth (prior observation : World → Prop) (truth : World)
    (hp : prior truth) (ho : observation truth) :
    prior truth ∧ observation truth := ⟨hp, ho⟩

theorem duplicate_idempotent (prior observation : World → Prop) (w : World) :
    ((prior w ∧ observation w) ∧ observation w) ↔ (prior w ∧ observation w) := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, h.2⟩

theorem accepted_action_sound (retained safe : World → Prop) (truth : World)
    (ht : retained truth) (ha : GuardedAcceptance retained safe) : safe truth :=
  ha.2 truth ht

theorem empty_set_blocks (safe : World → Prop) :
    ¬ GuardedAcceptance (fun _ => False) safe := by
  rintro ⟨⟨w, hw⟩, _⟩
  exact hw

theorem outer_universal_bound_sound (exact outer safe : World → Prop)
    (contained : ∀ w, exact w → outer w) (bound : ∀ w, outer w → safe w) :
    ∀ w, exact w → safe w := by
  intro w hw
  exact bound w (contained w hw)

theorem branch_complete_action_sound (branch : Branch → World → Prop)
    (safe : World → Prop) (nonempty : ∃ b w, branch b w)
    (checked : ∀ b w, branch b w → safe w) :
    GuardedAcceptance (fun w => ∃ b, branch b w) safe := by
  constructor
  · rcases nonempty with ⟨b, w, hw⟩
    exact ⟨w, b, hw⟩
  · rintro w ⟨b, hw⟩
    exact checked b w hw

theorem heldout_requires_one_joint_witness (branch : Branch → World → Prop)
    (heldout : World → Prop) :
    (∃ w, (∃ b, branch b w) ∧ heldout w) ↔
      ∃ b w, branch b w ∧ heldout w := by
  constructor
  · rintro ⟨w, ⟨b, hb⟩, hh⟩
    exact ⟨b, w, hb, hh⟩
  · rintro ⟨b, w, hb, hh⟩
    exact ⟨w, ⟨b, hb⟩, hh⟩

#print axioms update_preserves_truth
#print axioms duplicate_idempotent
#print axioms accepted_action_sound
#print axioms empty_set_blocks
#print axioms outer_universal_bound_sound
#print axioms branch_complete_action_sound
#print axioms heldout_requires_one_joint_witness
end S12Guarded
