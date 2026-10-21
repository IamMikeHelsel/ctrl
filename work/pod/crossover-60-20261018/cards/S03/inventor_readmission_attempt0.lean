import LeanControls.Quantized

noncomputable section
namespace S03Readmission
open LeanControls.PD LeanControls.SampledPD

theorem energy_young (x v ex ev : ℝ) :
    energy (x+ex) (v+ev) ≤ 1001/1000*energy x v+1001*energy ex ev := by
  have hp := energy_nonneg (x-1000*ex) (v-1000*ev)
  unfold energy at *
  nlinarith only [hp]

theorem error_energy {h d D : ℝ} (h0 : 0≤h) (hhi : h≤1/2)
    (hD : 0≤D) (hd : |d|≤D) :
    energy (h^2/2*d) (h*d) ≤ 29/64*D^2 := by
  have hh : h^2≤1/4 := by nlinarith
  have hd2 : d^2≤D^2 := by
    have := abs_le.mp hd
    nlinarith [sq_nonneg (D-d), sq_nonneg (D+d)]
  have hp : 0≤1+h+5/4*h^2 := by positivity
  have hp' : 1+h+5/4*h^2≤29/16 := by linarith
  have hprod := mul_le_mul hh hp' hp (by norm_num : (0:ℝ)≤1/4)
  have hmul := mul_le_mul_of_nonneg_right hprod (sq_nonneg d)
  have hmul' := mul_le_mul_of_nonneg_left hd2 (by norm_num : (0:ℝ)≤29/64)
  unfold energy
  nlinarith only [hmul, hmul']

theorem endpoint_margin {h x v d : ℝ} (hlo : 1/20≤h) (hhi : h≤1/2)
    (hE : energy x v≤1/10) (hd : |d|≤1/1250) :
    energy (position h x v+h^2/2*d) (velocity h x v+h*d) ≤ 29866837/300000000 := by
  have hn := LeanControls.Sampling.half_step_contract (by linarith : 0≤h) hhi x v
  have hm := mul_le_mul_of_nonneg_right
    (show 1-h/6≤119/120 by linarith) (energy_nonneg x v)
  have he := error_energy (by linarith : 0≤h) hhi (by norm_num : (0:ℝ)≤1/1250) hd
  have hy := energy_young (position h x v) (velocity h x v) (h^2/2*d) (h*d)
  nlinarith only [hn, hm, he, hy, hE]

theorem cell_lift {x v dx dv δ : ℝ}
    (hx : |x|≤4/25) (hv : |v|≤9/25)
    (hdx : |dx|≤δ) (hdv : |dv|≤δ) (hδ : 0≤δ) :
    energy (x+dx) (v+dv) ≤ energy x v+84/25*δ+8*δ^2 := by
  have hxx := abs_mul_le_abs_mul_right hx dx
  have hvx := abs_mul_le_abs_mul_right hv dx
  have hxv := abs_mul_le_abs_mul_right hx dv
  have hvv := abs_mul_le_abs_mul_right hv dv
  have h1 : x*dx≤4/25*δ := by
    calc x*dx ≤ |x*dx| := le_abs_self _
         _ = |x|*|dx| := abs_mul _ _
         _ ≤ (4/25)*δ := mul_le_mul hx hdx (abs_nonneg _) (by norm_num)
  have h2 : v*dx≤9/25*δ := by
    calc v*dx ≤ |v*dx| := le_abs_self _
         _ = |v|*|dx| := abs_mul _ _
         _ ≤ (9/25)*δ := mul_le_mul hv hdx (abs_nonneg _) (by norm_num)
  have h3 : x*dv≤4/25*δ := by
    calc x*dv ≤ |x*dv| := le_abs_self _
         _ = |x|*|dv| := abs_mul _ _
         _ ≤ (4/25)*δ := mul_le_mul hx hdv (abs_nonneg _) (by norm_num)
  have h4 : v*dv≤9/25*δ := by
    calc v*dv ≤ |v*dv| := le_abs_self _
         _ = |v|*|dv| := abs_mul _ _
         _ ≤ (9/25)*δ := mul_le_mul hv hdv (abs_nonneg _) (by norm_num)
  have h5 : dx^2≤δ^2 := by have := abs_le.mp hdx; nlinarith
  have h6 : dv^2≤δ^2 := by have := abs_le.mp hdv; nlinarith
  have h7 : dx*dv≤δ^2 := by nlinarith [sq_nonneg (dx-dv)]
  unfold energy
  nlinarith only [h1,h2,h3,h4,h5,h6,h7]

theorem decimal_margin :
    (29866837:ℝ)/300000000+84/25*(1/10000)+8*(1/10000)^2 < 1/10 := by norm_num

end S03Readmission
#print axioms S03Readmission.energy_young
#print axioms S03Readmission.error_energy
#print axioms S03Readmission.endpoint_margin
#print axioms S03Readmission.cell_lift
#print axioms S03Readmission.decimal_margin
