import ControlsLean.Vision.Homography
import Mathlib.Tactic
namespace V01Pixels
open Matrix ControlsLean.Vision
variable {K : Type*} [Field K]

theorem calibrated_transfer (H K1 K1inv K2 : Matrix (Fin 3) (Fin 3) K)
    (hk : K1inv*K1=1) (x1 x2 : Fin 3 → K) (c : K)
    (hr : x2=c • (H*ᵥx1)) :
    K2*ᵥx2=c • ((K2*H*K1inv)*ᵥ(K1*ᵥx1)) := by
  have hc : K1inv*ᵥ(K1*ᵥx1)=x1 := by rw [mulVec_mulVec,hk,one_mulVec]
  rw [hr,mulVec_smul]
  congr 1
  rw [← mulVec_mulVec,← mulVec_mulVec,hc]

/-- Source calibrated-plane relation transported through explicit intrinsic matrices. -/
theorem source_pixel_transfer (R K1 K1inv K2 : Matrix (Fin 3) (Fin 3) K)
    (hk : K1inv*K1=1) (t n x1 x2 : Fin 3 → K) (d a b : K)
    (hd : d≠0) (hb : b≠0)
    (hp : n ⬝ᵥ (a•x1)=d) (hr : b•x2=R*ᵥ(a•x1)+t) :
    K2*ᵥx2=(a/b) • ((K2*homographyPlane R t n d*K1inv)*ᵥ(K1*ᵥx1)) := by
  apply calibrated_transfer _ K1 K1inv K2 hk x1 x2 (a/b)
  have hh := plane_homography_constraint R t n d x1 x2 a b hd hp hr
  rw [mulVec_smul] at hh
  have hv := congrArg (fun z => b⁻¹ • z) hh
  simpa [smul_smul,inv_mul_cancel₀ hb,div_eq_mul_inv,mul_comm] using hv
end V01Pixels
#print axioms V01Pixels.calibrated_transfer
#print axioms V01Pixels.source_pixel_transfer
