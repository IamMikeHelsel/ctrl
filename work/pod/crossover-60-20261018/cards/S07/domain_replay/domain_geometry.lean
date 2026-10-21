import Mathlib.Tactic
namespace S07Domain
noncomputable def V (x v a : ℝ) : ℝ := (38/5)*x^2+(1319/50)*v^2+(278/25)*a^2+2*(257/25)*x*v+10*x*a+2*(769/50)*v*a
theorem input_sos (x v a : ℝ) : (4133475/11131832:ℝ)*V x v a-(-x-3*v-2*a)^2 =
  (10141289/5565916:ℝ)*(x+(9096627/20282578:ℝ)*v+(-1596289/20282578:ℝ)*a)^2+(24211284359139/56445562705724:ℝ)*(v+(-12683/24202:ℝ)*a)^2 := by unfold V; ring
theorem input_bound (x v a : ℝ) : (-x-3*v-2*a)^2 ≤ (4133475/11131832:ℝ)*V x v a := by
  have h := input_sos x v a
  have h0 : 0 ≤ (10141289/5565916:ℝ)*(x+(9096627/20282578:ℝ)*v+(-1596289/20282578:ℝ)*a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (24211284359139/56445562705724:ℝ)*(v+(-12683/24202:ℝ)*a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  linarith
theorem position_sos (x v a : ℝ) : (3550075/11131832:ℝ)*V x v a-x^2 =
  (7924369/5565916:ℝ)*(x+(36494771/15848738:ℝ)*v+(17750375/15848738:ℝ)*a)^2+(38095377836923/44106372207004:ℝ)*(v+(46767/32758:ℝ)*a)^2 := by unfold V; ring
theorem position_bound (x v a : ℝ) : x^2 ≤ (3550075/11131832:ℝ)*V x v a := by
  have h := position_sos x v a
  have h0 : 0 ≤ (7924369/5565916:ℝ)*(x+(36494771/15848738:ℝ)*v+(17750375/15848738:ℝ)*a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (38095377836923/44106372207004:ℝ)*(v+(46767/32758:ℝ)*a)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  linarith
theorem active_witness : V (15134/165339) (-50732/165339) (-96808/165339) = 44527328/4133475 ∧
  -(15134/165339:ℝ)-3*(-50732/165339)-2*(-96808/165339)=2 ∧ (44527328/4133475:ℝ)<12 := by norm_num [V]
theorem expanded_geometry (x v a : ℝ) (h : V x v a ≤ 44527328/3550075) :
  x^2 ≤ 4 ∧ (-x-3*v-2*a)^2 ≤ 16 := by
  have hp := position_bound x v a
  have hu := input_bound x v a
  constructor <;> nlinarith
theorem expanded_budget : (13:ℝ)*(1/5+(5/451)⁻¹)*(1/100)^2 ≤ (5/451)*(44527328/3550075) := by norm_num
end S07Domain
#print axioms S07Domain.input_sos
#print axioms S07Domain.input_bound
#print axioms S07Domain.position_sos
#print axioms S07Domain.position_bound
#print axioms S07Domain.active_witness
#print axioms S07Domain.expanded_geometry
#print axioms S07Domain.expanded_budget
