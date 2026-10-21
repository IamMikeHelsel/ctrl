import Mathlib.Tactic
namespace CampaignC03Septic
 theorem z_domain (y : ℝ) (h0 : 0≤y) (h1 : y≤1) : 0≤y*(1-y) ∧ y*(1-y)≤1/4 := by
  constructor
  · positivity
  · nlinarith [sq_nonneg (y-1/2)]
 theorem rate_identity (y : ℝ) :
 140*y^3-420*y^4+420*y^5-140*y^6 = 140*(y*(1-y))^3 := by ring
 theorem accel_identity (y : ℝ) :
 420*y^2-1680*y^3+2100*y^4-840*y^5 = 420*(y*(1-y))^2*(1-2*y) := by ring
 theorem jerk_identity (y : ℝ) :
 840*y-5040*y^2+8400*y^3-4200*y^4 = 840*(y*(1-y))*(1-5*(y*(1-y))) := by ring
 theorem snap_identity (y : ℝ) :
 840-10080*y+25200*y^2-16800*y^3 = 840*(1-2*y)*(1-10*(y*(1-y))) := by ring
 theorem jerk_bound (z : ℝ) (h0 : 0≤z) (h1 : z≤1/4) : |z*(1-5*z)|≤1/16 := by
  apply abs_le.mpr
  constructor
  · have h := mul_nonneg (show 0≤1/4-z by linarith) (show 0≤5*z+1/4 by linarith)
    nlinarith
  · nlinarith [sq_nonneg (z-1/10)]
 theorem snap_bound (r z : ℝ) (h0 : 0≤z) (hr : r^2=1-4*z) : |r*(1-10*z)|≤1 := by
  have he : 1-(r*(1-10*z))^2 = 4*z*(100*(z-9/40)^2+15/16) := by rw [mul_pow,hr]; ring
  have hp : 0≤4*z*(100*(z-9/40)^2+15/16) := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith
 theorem scaled_budgets :
 (35/16*(1/24000)/(1/10):ℝ)=7/7680 ∧
 (105/4*(1/24000)/(1/10)^2:ℝ)=7/64 ∧
 (105/2*(1/24000)/(1/10)^3:ℝ)=35/16 ∧
 (840*(1/24000)/(1/10)^4:ℝ)=350 := by norm_num
 theorem endpoints :
 (35-84+70-20:ℝ)=1 ∧ (140-420+420-140:ℝ)=0 ∧
 (420-1680+2100-840:ℝ)=0 ∧ (840-5040+8400-4200:ℝ)=0 := by norm_num
end CampaignC03Septic
#print axioms CampaignC03Septic.z_domain
#print axioms CampaignC03Septic.rate_identity
#print axioms CampaignC03Septic.accel_identity
#print axioms CampaignC03Septic.jerk_identity
#print axioms CampaignC03Septic.snap_identity
#print axioms CampaignC03Septic.jerk_bound
#print axioms CampaignC03Septic.snap_bound
#print axioms CampaignC03Septic.scaled_budgets
#print axioms CampaignC03Septic.endpoints
