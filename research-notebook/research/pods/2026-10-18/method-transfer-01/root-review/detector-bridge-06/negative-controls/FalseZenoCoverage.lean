import DetectorWitness
open LeanControls.DetectorSampling
example (n : ℕ) : (39/122:ℝ) ≤ zeno n := by
 have h := zeno_bounded n
 linarith
