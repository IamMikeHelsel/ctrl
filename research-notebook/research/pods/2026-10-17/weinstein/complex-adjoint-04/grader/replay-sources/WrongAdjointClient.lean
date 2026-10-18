import AdjointControls
open GUComplex
example : fixedBar (iAnti (cgamma 0) (cgamma 0)) = -iAnti (cgamma 0) (cgamma 0) := by
  exact iAnti_skew (cgamma 0) (cgamma 0) (gamma_skew 0) (gamma_skew 0)
