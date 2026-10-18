import ReviewClients
open LeanControls LeanControls.QuadraticHold LeanControls.QuadraticWitness LeanControls.QuadraticIndependentReview
example : energyRate 160 (-1) (-2) 2 (-1) ≤ 20*(1-energy (-2) 2 (-1)) := by
  norm_num [energy,energyRate,movingState,stepHold,DirectReference.reference_endpoint]
