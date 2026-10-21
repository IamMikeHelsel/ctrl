import Mathlib.Tactic
namespace V12Continuous
 theorem fraction_bound (n d : ℝ) (hn : |n|≤2/25) (hd : (499/100)^2≤d) : |n/d|≤33/10000 := by
  have hd0 : 0<d := by nlinarith
  rw [abs_div,abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  nlinarith

 theorem projection_difference (x y c s a : ℝ) (h1 : 5+s*y≠0) (h2 : 5+a*s*y≠0) :
  1000*x/(5+s*y)-1000*x/(5+a*s*y) = 1000*x*s*y*(a-1)/((5+s*y)*(5+a*s*y)) ∧
  1000*c*y/(5+s*y)-1000*a*c*y/(5+a*s*y) = 5000*c*y*(1-a)/((5+s*y)*(5+a*s*y)) := by
  constructor <;> rw [div_sub_div _ _ h1 h2] <;> congr 1 <;> ring

 theorem denominator_bound (s a y : ℝ) (hs : |s|≤1/500) (ha : |a|≤1) (hy : |y|≤1) :
  (499/100)^2≤(5+s*y)*(5+a*s*y) := by
  have hsy : |s*y|≤1/500 := by
   rw [abs_mul]; calc |s| * |y|≤(1/500)*1 := mul_le_mul hs hy (abs_nonneg _) (by norm_num)
                     _=1/500 := by ring
  have hasy : |a*s*y|≤1/500 := by
   rw [mul_assoc,abs_mul]; calc |a| * |s*y|≤1*(1/500) := mul_le_mul ha hsy (abs_nonneg _) (by norm_num)
                              _=1/500 := by ring
  rw [abs_le] at hsy hasy
  have hlo1 : 499/100≤5+s*y := by linarith
  have hlo2 : 499/100≤5+a*s*y := by linarith
  have hm := mul_le_mul hlo1 hlo2 (by norm_num : (0:ℝ)≤499/100) (by linarith : 0≤5+s*y)
  nlinarith

 theorem numerator_bound (x y c s a : ℝ) (hx : |x|≤1) (hy : |y|≤1)
  (hc : |c|≤1) (hs : |s|≤1) (ha : |1-a|≤1/62500) :
  |1000*x*s*y*(a-1)|≤2/25 ∧ |5000*c*y*(1-a)|≤2/25 := by
  have hae : |a-1|≤1/62500 := by simpa [abs_sub_comm] using ha
  constructor
  · rw [abs_mul,abs_mul,abs_mul,abs_mul]; norm_num
    calc 1000*|x| * |s| * |y| * |a-1| ≤1000*1*1*1*(1/62500) := by gcongr
         _≤2/25 := by norm_num
  · rw [abs_mul,abs_mul,abs_mul]; norm_num
    calc 5000*|c| * |y| * |1-a| ≤5000*1*1*(1/62500) := by gcongr
         _≤2/25 := by norm_num

 theorem whole_board (x y c s a : ℝ) (hx : |x|≤1) (hy : |y|≤1)
 (hc : |c|≤1) (hs : |s|≤1/500) (ha : |a|≤1) (hea : |1-a|≤1/62500)
 (h1 : 5+s*y≠0) (h2 : 5+a*s*y≠0) :
 |1000*x/(5+s*y)-1000*x/(5+a*s*y)|≤33/10000 ∧
 |1000*c*y/(5+s*y)-1000*a*c*y/(5+a*s*y)|≤33/10000 := by
  have hn := numerator_bound x y c s a hx hy hc (by linarith) hea
  have hd := denominator_bound s a y hs ha hy
  obtain ⟨hu,hv⟩ := projection_difference x y c s a h1 h2
  rw [hu,hv]
  exact ⟨fraction_bound _ _ hn.1 hd,fraction_bound _ _ hn.2 hd⟩
 theorem concrete_parameters :
 |(999999/1000001:ℝ)|≤1 ∧ |(2000/1000001:ℝ)|≤1/500 ∧
 |((999991/1000009)/(999999/1000001):ℝ)|≤1 ∧
 |1-((999991/1000009)/(999999/1000001):ℝ)|≤1/62500 ∧
 (6000/1000009:ℝ)/(2999997/999991)=((999991/1000009)/(999999/1000001))*(2000/1000001) := by norm_num
end V12Continuous
#print axioms V12Continuous.fraction_bound
#print axioms V12Continuous.projection_difference
#print axioms V12Continuous.denominator_bound
#print axioms V12Continuous.numerator_bound

#print axioms V12Continuous.whole_board
#print axioms V12Continuous.concrete_parameters
