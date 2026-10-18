import Client
noncomputable section
open scoped TensorProduct
open Matrix HyperbolicSpinor GUClifford GUComplex
example : (K *ᵥ unitCoord ∅) ∅ = 1 := by
  rw [K_vacuum_column]
  have hn : (∅ : Finset J) ≠ Finset.univ := by
    intro h
    have hh : (0 : J) ∈ (∅ : Finset J) := h.symm ▸ Finset.mem_univ 0
    simp at hh
  simp [unitCoord, Pi.single_apply, hn]
