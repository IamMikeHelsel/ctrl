import ReviewClients
open LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview
example : energyRate 80 2 2 0 0 ≤ 20*(1-energy 2 0 0) := by
  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]
