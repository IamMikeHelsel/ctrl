import ReviewClients
open LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview
example : movingState 0 = DirectReference.reference 7 (DirectReference.duration 7) := by
  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]
