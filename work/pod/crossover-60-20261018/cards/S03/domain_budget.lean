import LeanControls.Quantized
noncomputable section
namespace S03Budget
open LeanControls.PD LeanControls.SampledPD LeanControls.Quantized

/-- Reuse the source contraction exactly; D is a total delivered acceleration error. -/
theorem safe_step {h x v u w D : ℝ}
    (hlo : 1/20≤h) (hhi : h≤1/2) (hE : energy x v≤1/10)
    (herr : |u-control x v|+|w|≤D)
    (budget : 1446*(3/5*D)^2≤1/2400) :
    energy (x+h*v+h^2/2*(u+w)) (v+h*(u+w))≤1/10 := by
  let d := u-control x v+w
  have hd : |d|≤D := (abs_add_le _ _).trans herr
  have he := integrated_error (by linarith : 0≤h) hhi hd
  have hb := LeanControls.Sampling.robust_step (x:=x) (v:=v) hlo hhi he
  have hp : x+h*v+h^2/2*(u+w)=position h x v+h^2/2*d := by dsimp[position,d]; ring
  have hv : v+h*(u+w)=velocity h x v+h*d := by dsimp[velocity,d]; ring
  rw [hp,hv]
  nlinarith only [hb,hE,budget]

theorem widened_budget : 1446*((3:ℝ)/5*(1/1250))^2≤1/2400 := by norm_num

theorem narrower_slack : (5:ℝ)/(2*10000)+1/4000+3/10000=1/1250 := by norm_num
end S03Budget
#print axioms S03Budget.safe_step
#print axioms S03Budget.widened_budget
#print axioms S03Budget.narrower_slack
