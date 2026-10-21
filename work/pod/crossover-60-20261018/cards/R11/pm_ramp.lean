import Mathlib.Data.Real.Basic

import Mathlib.Tactic

namespace CampaignR11Ramp

theorem energy_step (x y z:ℝ) : ((1785/158:ℝ)*(x-y/10-z/10)*(x-y/10-z/10)+(-135/79:ℝ)*(x-y/10-z/10)*(x)+(-303/316:ℝ)*(x-y/10-z/10)*(y)+(-135/79:ℝ)*(x)*(x-y/10-z/10)+(191/79:ℝ)*(x)*(x)+(33/158:ℝ)*(x)*(y)+(-303/316:ℝ)*(y)*(x-y/10-z/10)+(33/158:ℝ)*(y)*(x)+(3517/3160:ℝ)*(y)*(y)) = ((1785/158:ℝ)*(x)*(x)+(-135/79:ℝ)*(x)*(y)+(-303/316:ℝ)*(x)*(z)+(-135/79:ℝ)*(y)*(x)+(191/79:ℝ)*(y)*(y)+(33/158:ℝ)*(y)*(z)+(-303/316:ℝ)*(z)*(x)+(33/158:ℝ)*(z)*(y)+(3517/3160:ℝ)*(z)*(z))-(x^2+y^2+z^2) := by ring

theorem energy_lower (x y z:ℝ) : (1/2:ℝ)*(x^2+y^2+z^2) ≤ ((1785/158:ℝ)*(x)*(x)+(-135/79:ℝ)*(x)*(y)+(-303/316:ℝ)*(x)*(z)+(-135/79:ℝ)*(y)*(x)+(191/79:ℝ)*(y)*(y)+(33/158:ℝ)*(y)*(z)+(-303/316:ℝ)*(z)*(x)+(33/158:ℝ)*(z)*(y)+(3517/3160:ℝ)*(z)*(z)) := by
  have h0 : 0 ≤ (853/79:ℝ)*(x+(-135/853:ℝ)*y+(-303/3412:ℝ)*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (222009/134774:ℝ)*(y+(5131/148006:ℝ)*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (3113123/5920240:ℝ)*z^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0,h1,h2]

theorem energy_upper (x y z:ℝ) : ((1785/158:ℝ)*(x)*(x)+(-135/79:ℝ)*(x)*(y)+(-303/316:ℝ)*(x)*(z)+(-135/79:ℝ)*(y)*(x)+(191/79:ℝ)*(y)*(y)+(33/158:ℝ)*(y)*(z)+(-303/316:ℝ)*(z)*(x)+(33/158:ℝ)*(z)*(y)+(3517/3160:ℝ)*(z)*(z)) ≤ 20*(x^2+y^2+z^2) := by
  have h0 : 0 ≤ (1375/158:ℝ)*(x+(54/275:ℝ)*y+(303/2750:ℝ)*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (74937/4345:ℝ)*(y+(-2876/124895:ℝ)*z)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (11722789/624475:ℝ)*z^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0,h1,h2]

theorem initial_energy : ((1785/158:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(-135/79:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(-303/316:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(-135/79:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(191/79:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(33/158:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(-303/316:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(33/158:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))+(3517/3160:ℝ)*((1/10000:ℝ))*((1/10000:ℝ))) ≤ (1/2:ℝ)*(1/1000)^2 := by norm_num

theorem energy_contraction (E En S : ℝ) (hd : En=E-S) (hu : E ≤ 20*S) : En ≤ (19/20:ℝ)*E := by linarith

theorem ramp_integral_step (x y z:ℝ) : x+(1/50:ℝ)*((-10*z)+(-10*y))/2 = x-y/10-z/10 := by ring

theorem ramp_acceleration (y z:ℝ) (hy:|y|≤1/1000) (hz:|z|≤1/1000) : |((-10*y)-(-10*z))/(1/50)|≤1 := by
 rw [abs_le] at hy hz ⊢
 constructor <;> linarith

end CampaignR11Ramp

#print axioms CampaignR11Ramp.energy_step

#print axioms CampaignR11Ramp.energy_lower

#print axioms CampaignR11Ramp.energy_upper

#print axioms CampaignR11Ramp.initial_energy

#print axioms CampaignR11Ramp.energy_contraction

#print axioms CampaignR11Ramp.ramp_integral_step

#print axioms CampaignR11Ramp.ramp_acceleration
