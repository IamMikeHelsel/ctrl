import Mathlib.Tactic
namespace R07PM
/-- Declared fixed-acceleration braking polynomial. ODE/controller binding is separate. -/
theorem braking_envelope (q v d t : ℝ) :
    q+v*d+v*t-t^2/20 ≤ q+v*d+5*v^2 := by
  nlinarith [sq_nonneg (t-10*v)]

theorem reserve_endpoint (q v d : ℝ)
    (hq : q≤9/50) (hv0 : 0≤v) (hv : v≤1/5)
    (hd0 : 0≤d) (hd : d≤1/20) :
    q+v*d+5*v^2 ≤ 39/100 := by
  have hp := mul_nonneg (show 0≤1/5-v by linarith) (show 0≤1/5+v by linarith)
  have hprod := mul_le_mul hv hd hd0 (by norm_num : (0:ℝ)≤1/5)
  nlinarith

theorem braking_box (q v d t : ℝ)
    (hq0 : 17/100≤q) (hq : q≤9/50) (hv0 : 0≤v) (hv : v≤1/5)
    (hd0 : 0≤d) (hd : d≤1/20) (ht0 : 0≤t) (ht : t≤10*v) :
    17/100≤q+v*d+v*t-t^2/20 ∧ q+v*d+v*t-t^2/20≤39/100 := by
  have hp := mul_nonneg ht0 (show 0≤20*v-t by linarith)
  have hvd := mul_nonneg hv0 hd0
  constructor
  · nlinarith
  · exact le_trans (braking_envelope q v d t) (reserve_endpoint q v d hq hv0 hv hd0 hd)

theorem delayed_coast_box (q v s : ℝ)
    (hq0 : 17/100≤q) (hq : q≤9/50) (hv0 : 0≤v) (hv : v≤1/5)
    (hs0 : 0≤s) (hs : s≤1/20) :
    17/100≤q+v*s ∧ q+v*s≤19/100 := by
  have hp := mul_le_mul hv hs hs0 (by norm_num : (0:ℝ)≤1/5)
  have hn := mul_nonneg hv0 hs0
  constructor <;> nlinarith

theorem position_contract (q : ℝ) (hl : 17/100≤q) (hu : q≤39/100) :
    q+(-q)=0 ∧ -1≤q ∧ q≤1 ∧ -1≤-q ∧ -q≤1 ∧ q-(-q)≤4/5-1/50 := by
  refine ⟨by ring, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem stop_join (q v d : ℝ) :
    q+v*d+v*(10*v)-(10*v)^2/20=q+v*d+5*v^2 ∧ v-(10*v)/10=0 := by
  constructor <;> ring

theorem inertia_and_torque :
    (-1/10:ℝ)+(1/5)/2=0 ∧ |(-1/10:ℝ)|≤1/10 ∧ |(1/5:ℝ)|≤1/5 := by norm_num

#print axioms braking_envelope
#print axioms reserve_endpoint
#print axioms braking_box
#print axioms delayed_coast_box
#print axioms position_contract
#print axioms stop_join
#print axioms inertia_and_torque
end R07PM
