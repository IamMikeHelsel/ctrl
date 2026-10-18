import FinalControls
namespace E11Critic
open Erdos128 Erdos128.FinalControls

/-- The triangle-free odd cycle has no cut with zero internal edges. -/
theorem cycle5_no_zero_cut :
    ¬ HasNormalizedInternalCutBoundQ cycle5 0 := by
  unfold HasNormalizedInternalCutBoundQ
  decide +kernel

/-- The zero-fold blowup discards the graph entirely. -/
theorem zero_blowup_zero_cut :
    HasNormalizedInternalCutBoundQ (balancedBlowup cycle5 0) 0 := by
  refine ⟨∅, ?_⟩
  simp [normalizedInternalCutCostQ]

/-- Positive blowup multiplicity is essential to the general descent lemma. -/
theorem positive_blowup_needed :
    ¬ (HasNormalizedInternalCutBoundQ (balancedBlowup cycle5 0) 0 ↔
      HasNormalizedInternalCutBoundQ cycle5 0) := by
  intro h
  exact cycle5_no_zero_cut (h.mp zero_blowup_zero_cut)

end E11Critic
#print axioms E11Critic.cycle5_no_zero_cut
#print axioms E11Critic.zero_blowup_zero_cut
#print axioms E11Critic.positive_blowup_needed
