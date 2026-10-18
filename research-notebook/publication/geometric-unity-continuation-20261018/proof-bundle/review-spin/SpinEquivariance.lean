import Chirality
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- Actual full volume commutes with every element of the even algebra. -/
theorem chirality_commutes_even (x : Cl) (hx : x ∈ CliffordAlgebra.even Q) :
    chirality * x = x * chirality := by
  change x ∈ CliffordAlgebra.evenOdd Q 0 at hx
  induction x, hx using CliffordAlgebra.even_induction Q with
  | algebraMap r => exact (Algebra.commutes r chirality).symm
  | add x y hx hy ihx ihy => simp only [mul_add, add_mul, ihx, ihy]
  | ι_mul_ι_mul v w x hx ih =>
    calc
      chirality * (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w * x) =
          (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) * (chirality * x) := by
            rw [← mul_assoc, chirality_commutes_bivector, mul_assoc]
      _ = (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w * x) * chirality := by rw [ih]; simp only [mul_assoc]

/-- Uses mathlib's explicitly defined spinGroup, a subgroup of even unitary versors. -/
theorem chirality_commutes_spin (s : Cl) (hs : s ∈ spinGroup Q) :
    chirality * s = s * chirality :=
  chirality_commutes_even s (spinGroup.mem_even hs)

/-- Group-level conjugation, not just infinitesimal bivector equivariance. -/
theorem spin_conjugation_twist (s : Cl) (hs : s ∈ spinGroup Q) (x : Cl) :
    s * (chirality * x) * star s = chirality * (s * x * star s) := by
  rw [← mul_assoc s, ← chirality_commutes_spin s hs]
  simp only [mul_assoc]

/-- The skew locus is stable under the actual unitary Spin conjugation. -/
theorem spin_conjugation_skew (s : Cl) (_hs : s ∈ spinGroup Q)
    (x : Cl) (hx : CliffordSkew x) : CliffordSkew (s*x*star s) := by
  dsimp [CliffordSkew] at hx ⊢
  rw [star_mul, star_mul, star_star, hx]
  simp only [mul_neg, neg_mul, mul_assoc]

/-- Two real skew vector images are transported by the same Spin conjugation. -/
theorem spin_twisted_vector_skew (s : Cl) (hs : s ∈ spinGroup Q) (v : V) :
    CliffordSkew (chirality * (s * CliffordAlgebra.ι Q v * star s)) := by
  rw [← spin_conjugation_twist s hs]
  exact spin_conjugation_skew s hs _ (chirality_twisted_vector_skew v)

/-- The conjugated argument is again an actual vector; no normalizer premise is added. -/
theorem spin_vector_conjugation_exists (s : spinGroup Q) (v : V) :
    ∃ w : V, CliffordAlgebra.ι Q w = (s : Cl) * CliffordAlgebra.ι Q v * star (s : Cl) := by
  let u : Clˣ := spinGroup.toUnits s
  have hu : (u : Cl) ∈ spinGroup Q := s.property
  have h := spinGroup.conjAct_smul_ι_mem_range_ι hu v
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨w, hw⟩

/-- Both choices transform with the same actual vector argument. -/
theorem spin_vector_choices_equivariant (s : spinGroup Q) (v : V) :
    ∃ w : V,
      CliffordAlgebra.ι Q w = (s : Cl) * CliffordAlgebra.ι Q v * star (s : Cl) ∧
      chirality * CliffordAlgebra.ι Q w =
        (s : Cl) * (chirality * CliffordAlgebra.ι Q v) * star (s : Cl) := by
  obtain ⟨w, hw⟩ := spin_vector_conjugation_exists s v
  exact ⟨w, hw, by rw [hw, spin_conjugation_twist _ s.property]⟩

end HyperbolicSpinor
