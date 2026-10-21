import ControlsLean.Vision.Homography
import Mathlib.Tactic
namespace V01Projective
open Matrix ControlsLean.Vision
variable {K : Type*} [Field K]

/-- Equality up to a declared scale is preserved and reflected by an invertible action. -/
theorem scalar_relation_iff (H G : Matrix (Fin 3) (Fin 3) K) (hg : G*H=1)
    (p q : Fin 3 → K) (c : K) :
    H*ᵥp=c • (H*ᵥq) ↔ p=c • q := by
  constructor
  · intro h
    have hh := congrArg (fun z => G*ᵥz) h
    simpa [mulVec_smul,mulVec_mulVec,hg] using hh
  · intro h
    rw [h,mulVec_smul]

/-- Nonzero lines remain genuine lines under the source contragredient action. -/
theorem line_nonzero (H G : Matrix (Fin 3) (Fin 3) K) (hg : G*H=1)
    (l : Fin 3 → K) (hl : l≠0) : lineTransform G l≠0 := by
  intro h
  have hh := congrArg (fun z => Hᵀ*ᵥz) h
  have hi : Hᵀ*Gᵀ=1 := by rw [← transpose_mul,hg,transpose_one]
  unfold lineTransform at hh
  rw [mulVec_mulVec,hi,one_mulVec,mulVec_zero] at hh
  exact hl hh
end V01Projective
#print axioms V01Projective.scalar_relation_iff
#print axioms V01Projective.line_nonzero
