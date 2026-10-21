import Mathlib.Tactic
namespace CampaignS07Quotient
 theorem request_hidden (x v a d : ℝ) : -(x+d)-3*(v-d)-2*(a+d) = -x-3*v-2*a := by ring
 theorem quotient_ode (v a u : ℝ) : a+(-a+u)=u ∧ v+a=v+a := by constructor <;> ring
 theorem request_ode (v a u : ℝ) : -v-3*a-2*(-a+u)=-(v+a)-2*u := by ring
 theorem held_quotient (x v a u t e : ℝ) :
 (x+t*v+u*t^2/2+(a-u)*(t-1+e))+(v+u*t+(a-u)*(1-e)) =
 (x+v)+t*(v+a)+u*t^2/2 ∧
 (v+u*t+(a-u)*(1-e))+(u+(a-u)*e) = (v+a)+u*t := by constructor <;> ring
 theorem held_request (x v a u t e : ℝ) :
 -(x+t*v+u*t^2/2+(a-u)*(t-1+e))-3*(v+u*t+(a-u)*(1-e))-2*(u+(a-u)*e) =
 (-x-3*v-2*a)-t*(v+a)-u*(2*t+t^2/2) := by ring
 theorem held_hidden (x v a u t e d : ℝ) :
 ((x+d)+t*(v-d)+u*t^2/2+((a+d)-u)*(t-1+e)) =
 (x+t*v+u*t^2/2+(a-u)*(t-1+e))+d*e ∧
 ((v-d)+u*t+((a+d)-u)*(1-e))=(v+u*t+(a-u)*(1-e))-d*e ∧
 (u+((a+d)-u)*e)=(u+(a-u)*e)+d*e := by constructor; ring; constructor <;> ring
 theorem lag_mismatch (a u rate : ℝ) : a+rate*(-a+u)=u+(1-rate)*(a-u) := by ring
 theorem capsule_budget :
 (13*((1/5)+(5/451)⁻¹)*(1/100)^2:ℝ)≤(5/451)*11 ∧
 (11*(3550075/11131832):ℝ)≤(15/8)^2 ∧
 (11*(4133475/11131832):ℝ)<16 := by norm_num
 theorem hidden_energy (x v a d : ℝ) :
 (38/5)*(x+d)^2+2*(257/25)*(x+d)*(v-d)+10*(x+d)*(a+d)+
 (1319/50)*(v-d)^2+2*(769/50)*(v-d)*(a+d)+(278/25)*(a+d)^2 =
 ((38/5)*x^2+2*(257/25)*x*v+10*x*a+(1319/50)*v^2+2*(769/50)*v*a+(278/25)*a^2)+
 2*d*((58/25)*x-(18/25)*v+(37/50)*a)+(189/50)*d^2 := by ring
 theorem capsule_outside :
 (189/50*(17/10)^2:ℝ)≤11 ∧
 (189/50*(73/40)^2:ℝ)>12 ∧
 (189/50*(73/40)^2:ℝ)>44527328/3550075 ∧
 (17/10+1/8:ℝ)=73/40 := by norm_num
 theorem capsule_position (x d e : ℝ) (hx : |x|≤15/8) (hd : |d|≤1/8) (he0 : 0≤e) (he1 : e≤1) : |x+d*e|≤2 := by
  have he : |e|≤1 := by rw [abs_of_nonneg he0]; exact he1
  have hde : |d*e|≤1/8 := by
   rw [abs_mul]
   have hm := mul_le_mul hd he (abs_nonneg _) (by norm_num : (0:ℝ)≤1/8)
   norm_num at hm
   exact hm
  have h := abs_add_le x (d*e)
  linarith
end CampaignS07Quotient
#print axioms CampaignS07Quotient.request_hidden
#print axioms CampaignS07Quotient.quotient_ode
#print axioms CampaignS07Quotient.request_ode
#print axioms CampaignS07Quotient.held_quotient
#print axioms CampaignS07Quotient.held_request
#print axioms CampaignS07Quotient.held_hidden
#print axioms CampaignS07Quotient.lag_mismatch
#print axioms CampaignS07Quotient.capsule_budget
#print axioms CampaignS07Quotient.hidden_energy
#print axioms CampaignS07Quotient.capsule_outside
#print axioms CampaignS07Quotient.capsule_position
