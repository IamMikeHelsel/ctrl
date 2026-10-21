import ControlsLean.Vision.Homography
import Mathlib.Tactic
noncomputable section
namespace V01Domain
open Matrix ControlsLean.Vision
variable {K : Type*} [Field K]

 theorem plane_nonzero (n x : Fin 3 → K) (d a : K) (hd : d≠0)
    (hp : n ⬝ᵥ (a • x)=d) : a≠0 ∧ x≠0 ∧ n≠0 := by
  refine ⟨?_,?_,?_⟩
  · intro h; apply hd; simpa [h] using hp.symm
  · intro h; apply hd; simpa [h] using hp.symm
  · intro h; apply hd; simpa [h] using hp.symm

 theorem image_nonzero (H G : Matrix (Fin 3) (Fin 3) K)
    (hg : G*H=1) {x : Fin 3 → K} (hx : x≠0) : H*ᵥx≠0 := by
  intro h
  have hh := congrArg (fun y => G*ᵥy) h
  rw [mulVec_mulVec, hg, one_mulVec, mulVec_zero] at hh
  exact hx hh

 theorem scaled_ray (R : Matrix (Fin 3) (Fin 3) K) (t n x1 x2 : Fin 3 → K)
    (d a b : K) (hd : d≠0) (hb : b≠0)
    (hp : n ⬝ᵥ (a • x1)=d) (hr : b • x2=R*ᵥ(a•x1)+t) :
    a/b≠0 ∧ x2=(a/b) • (homographyPlane R t n d*ᵥx1) := by
  have ha := (plane_nonzero n x1 d a hd hp).1
  refine ⟨div_ne_zero ha hb,?_⟩
  have hh := plane_homography_constraint R t n d x1 x2 a b hd hp hr
  rw [mulVec_smul] at hh
  have hv := congrArg (fun z => b⁻¹ • z) hh
  simpa [smul_smul, inv_mul_cancel₀ hb, div_eq_mul_inv, mul_comm] using hv

 theorem second_nonzero (R G : Matrix (Fin 3) (Fin 3) K) (t n x1 x2 : Fin 3 → K)
    (d a b : K) (hd : d≠0) (hg : G*homographyPlane R t n d=1)
    (hp : n ⬝ᵥ (a•x1)=d) (hr : b•x2=R*ᵥ(a•x1)+t) : b≠0 ∧ x2≠0 := by
  have hn : a•x1≠0 := by intro h; apply hd; simpa [h] using hp.symm
  have hi := image_nonzero _ G hg hn
  have hh := plane_homography_constraint R t n d x1 x2 a b hd hp hr
  have hs : b•x2≠0 := by rw [hh]; exact hi
  constructor
  · intro h; apply hs; simp [h]
  · intro h; apply hs; simp [h]

 theorem incidence_rescaling (H G : Matrix (Fin 3) (Fin 3) K)
    (hg : G*H=1) (l p : Fin 3 → K) (a b : K) (ha : a≠0) (hb : b≠0) :
    ((a • lineTransform G l) ⬝ᵥ (b • (H*ᵥp))=0) ↔ l ⬝ᵥ p=0 := by
  rw [smul_dotProduct, dotProduct_smul, lineTransform_dotProduct H G hg]
  simp [smul_eq_mul, mul_eq_zero, ha, hb]
end V01Domain
#print axioms V01Domain.plane_nonzero
#print axioms V01Domain.image_nonzero
#print axioms V01Domain.scaled_ray
#print axioms V01Domain.second_nonzero
#print axioms V01Domain.incidence_rescaling
