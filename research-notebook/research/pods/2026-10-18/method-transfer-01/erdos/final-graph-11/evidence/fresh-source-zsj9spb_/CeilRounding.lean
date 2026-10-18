import FinalControls
open scoped BigOperators
open Erdos128 Erdos128.FinalControls Erdos128.FiniteProfileBridge Erdos128.CompletionBridge
example : ∃ S : Finset (Fin 5), S.card=3 ∧ (edgeCountOn Erdos128.FinalControls.cycle5 S:ℚ)≤E10.R*25 := by
 have h := Erdos128.FinalControls.odd_ceil_impossible
 simp_all
