import LeanControls.Quantized
noncomputable section
namespace S03Domain
open LeanControls.PD LeanControls.SampledPD LeanControls.RobustPD LeanControls.Quantized

/-- Any delivered held input satisfying this total error contract inherits the source step. -/
theorem safe_step {h x v u w : ℝ}
    (hlo : 1/20 ≤ h) (hhi : h ≤ 1/2)
    (hE : energy x v ≤ 1/10)
    (herr : |u-control x v|+|w| ≤ 1/2000) :
    energy (x+h*v+h^2/2*(u+w)) (v+h*(u+w)) ≤ 1/10 := by
  let d := u-control x v+w
  have hd : |d| ≤ 1/2000 := (abs_add_le _ _).trans herr
  have he := integrated_error (by linarith : 0≤h) hhi hd
  have he' : (h^2/2*d)^2+(h*d)^2 ≤ (3/10000:ℝ)^2 := by norm_num at he ⊢; exact he
  have hb := LeanControls.Sampling.robust_step (x:=x) (v:=v) hlo hhi he'
  have hp : x+h*v+h^2/2*(u+w) = position h x v+h^2/2*d := by dsimp [position,d]; ring
  have hv : v+h*(u+w) = velocity h x v+h*d := by dsimp [velocity,d]; ring
  rw [hp,hv]
  nlinarith only [hb,hE]

/-- Endpoint induction retains the actual command sequence and true state. -/
theorem safe_trajectory (h x v u w : ℕ → ℝ)
    (hlo : ∀ n,1/20≤h n) (hhi : ∀ n,h n≤1/2)
    (herr : ∀ n, |u n-control (x n) (v n)|+|w n|≤1/2000)
    (hinit : energy (x 0) (v 0)≤1/10)
    (hx : ∀ n,x (n+1)=x n+h n*v n+(h n)^2/2*(u n+w n))
    (hv : ∀ n,v (n+1)=v n+h n*(u n+w n)) :
    ∀ n,energy (x n) (v n)≤1/10 := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih => rw [hx n,hv n]; exact safe_step (hlo n) (hhi n) ih (herr n)

/-- ADC state error and arithmetic error are measured against the same current true state. -/
theorem raw_error {x v xd vd a Ex Ev Ea : ℝ}
    (hx : |xd-x|≤Ex) (hv : |vd-v|≤Ev)
    (ha : |a-control xd vd|≤Ea) : |a-control x v|≤2*Ex+3*Ev+Ea := by
  have hxx := abs_le.mp hx
  have hvv := abs_le.mp hv
  have haa := abs_le.mp ha
  apply abs_le.mpr
  unfold LeanControls.SampledPD.control at *
  constructor <;> linarith

/-- Exact real clamp followed by a bounded delivered-output error; no overflow assumption is hidden. -/
theorem delivered_error {x v xd vd a u Ex Ev Ea Ed : ℝ}
    (hE : energy x v≤1/10)
    (hx : |xd-x|≤Ex) (hv : |vd-v|≤Ev)
    (ha : |a-control xd vd|≤Ea)
    (hu : |u-saturate 1 a|≤Ed) :
    |u-control x v|≤2*Ex+3*Ev+Ea+Ed := by
  have hn := control_within_limit (by norm_num : (0:ℝ)≤1) hE (by norm_num)
  have hr := raw_error hx hv ha
  have hc := clipping_error (e:=a-control x v) hn
  have hi : control x v+(a-control x v)=a := by ring
  rw [hi] at hc
  have ht : |u-control x v|≤|u-saturate 1 a|+|saturate 1 a-control x v| := by
    simpa using abs_add_le (u-saturate 1 a) (saturate 1 a-control x v)
  linarith

/-- Actual post-clamp error is part of the same finite implementation budget. -/
theorem implementation_step {h x v xd vd a u w Ex Ev Ea Ed W : ℝ}
    (hlo : 1/20≤h) (hhi : h≤1/2) (hE : energy x v≤1/10)
    (hx : |xd-x|≤Ex) (hv : |vd-v|≤Ev)
    (ha : |a-control xd vd|≤Ea) (hu : |u-saturate 1 a|≤Ed)
    (hw : |w|≤W) (budget : 2*Ex+3*Ev+Ea+Ed+W≤1/2000) :
    energy (x+h*v+h^2/2*(u+w)) (v+h*(u+w))≤1/10 := by
  apply safe_step hlo hhi hE
  have hh := delivered_error hE hx hv ha hu
  linarith
end S03Domain
#print axioms S03Domain.safe_step
#print axioms S03Domain.safe_trajectory
#print axioms S03Domain.raw_error
#print axioms S03Domain.delivered_error
#print axioms S03Domain.implementation_step
