import ProfileControls
open Erdos128 Erdos128.ProfileBridge Erdos128.ProfileControls
example : IsUnitProfile (lowProfile edge halves (4 / 5) 0) := by
  have h := wrong_low_branch_not_unit
  simp_all
