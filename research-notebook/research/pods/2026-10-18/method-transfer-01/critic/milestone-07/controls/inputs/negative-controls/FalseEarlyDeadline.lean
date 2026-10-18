import DelayedWitness
open LeanControls.DelayedEntry LeanControls.DelayedEntry.Witness LeanControls.WeightedEntry
example : envelope delay entryTime ≤ target := by
 have h := deadline_requires_delay
 linarith
