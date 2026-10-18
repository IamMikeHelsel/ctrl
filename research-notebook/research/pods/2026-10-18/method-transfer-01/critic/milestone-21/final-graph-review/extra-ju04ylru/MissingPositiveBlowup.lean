import ReviewControls
open Erdos128 Erdos128.FinalControls E11Critic
example : HasNormalizedInternalCutBoundQ (balancedBlowup cycle5 0) 0 ↔
    HasNormalizedInternalCutBoundQ cycle5 0 := by
  have h := positive_blowup_needed
  simp_all
