import CliffordControls
open GUClifford
example : K fourform = algebraMap ℝ Cl (-scal fourform) := by
  exact actual_clifford_contraction fourform fourform_pair
