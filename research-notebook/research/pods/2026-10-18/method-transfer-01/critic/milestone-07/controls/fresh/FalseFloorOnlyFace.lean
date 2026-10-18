import RateAndClockScope
open LeanControls DigitalHold WeightedEntry
example : transformedRHS 16 DelayedEntry.residual
    ![-(51/50)*target,(101/100)*target,target] 2 ≤ -drift := by
  have h := CriticC4.floor_only_face_outward.2
  norm_num [drift] at *
  linarith
