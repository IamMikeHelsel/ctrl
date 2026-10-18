import TranslatedScope
open CriticAdmission
example : shiftedState 0 0 ≤ (3/20 : ℝ) := by
 have h := translated_execution_rejects_absolute_clearance.2.2.2.2
 linarith
