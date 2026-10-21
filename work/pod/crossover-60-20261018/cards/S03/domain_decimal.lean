import domain_contract
import domain_range
import domain_budget
noncomputable section
namespace S03Decimal
open LeanControls.PD LeanControls.SampledPD LeanControls.RobustPD LeanControls.Quantized

/-- This is unbounded integer decoding; bounded-word fidelity is a separate implementation proof. -/
theorem decoded_dot (X V : ℤ) :
    (((-2*X-3*V:ℤ):ℝ)/10000)=control ((X:ℝ)/10000) ((V:ℝ)/10000) := by
  push_cast
  unfold LeanControls.SampledPD.control
  ring

/-- Exact retained previous-hold motion, with a single acceleration b before current capture. -/
theorem stale_identity {xs vs x v tau b : ℝ}
    (hx : x=xs+tau*vs+tau^2/2*b) (hv : v=vs+tau*b) :
    control xs vs-control x v=2*tau*v+(3*tau-tau^2)*b := by
  rw [hx,hv]
  unfold LeanControls.SampledPD.control
  ring

/-- Shared acceleration is retained; replacing it by separate coordinate boxes loses the minus term. -/
theorem stale_bound {xs vs x v tau b : ℝ}
    (hE : energy x v≤1/10) (ht : 0≤tau) (htop : tau≤1/2)
    (hb : |b|≤4001/4000)
    (hx : x=xs+tau*vs+tau^2/2*b) (hv : v=vs+tau*b) :
    |control xs vs-control x v|≤(14883/4000)*tau-(4001/4000)*tau^2 := by
  rw [stale_identity hx hv]
  have hc : 0≤3*tau-tau^2 := by nlinarith
  have vv := abs_le.mp (S03Range.invariant_ranges hE).2.1
  have bb := abs_le.mp hb
  have p1 := mul_le_mul_of_nonneg_left vv.1 (show 0≤2*tau by positivity)
  have p2 := mul_le_mul_of_nonneg_left vv.2 (show 0≤2*tau by positivity)
  have p3 := mul_le_mul_of_nonneg_left bb.1 hc
  have p4 := mul_le_mul_of_nonneg_left bb.2 hc
  apply abs_le.mpr
  constructor <;> nlinarith only [p1,p2,p3,p4]

theorem age_allowance {tau : ℝ} (ht : 0≤tau) (htop : tau≤1/20000) :
    (14883/4000)*tau-(4001/4000)*tau^2≤3/16000 := by
  nlinarith [sq_nonneg tau]

/-- One concrete joint contract: decimal half cells, exact dot, bounded DAC, retained age. -/
theorem decimal_step {h xs vs x v tau b xd vd a u w : ℝ}
    (hlo : 1/20≤h) (hhi : h≤1/2) (hE : energy x v≤1/10)
    (ht : 0≤tau) (htop : tau≤1/20000) (hb : |b|≤4001/4000)
    (hx : x=xs+tau*vs+tau^2/2*b) (hv : v=vs+tau*b)
    (hxd : |xd-xs|≤1/20000) (hvd : |vd-vs|≤1/20000)
    (ha : a=control xd vd) (hu : |u-saturate 1 a|≤1/10000)
    (hw : |w|≤1/4000) :
    energy (x+h*v+h^2/2*(u+w)) (v+h*(u+w))≤1/10 ∧ |u|≤1 := by
  have hq : |a-control xs vs|≤1/4000 := by
    have hzero : |a-control xd vd|≤0 := by rw [ha]; simp
    have hh := S03Domain.raw_error hxd hvd hzero
    norm_num at hh
    exact hh
  have hs := stale_bound hE ht (by linarith : tau≤1/2) hb hx hv
  have hs' : |control xs vs-control x v|≤3/16000 := hs.trans (age_allowance ht htop)
  have hr : |a-control x v|≤1/4000+3/16000 := by
    have hh := abs_add_le (a-control xs vs) (control xs vs-control x v)
    have hid : a-control xs vs+(control xs vs-control x v)=a-control x v := by ring
    rw [hid] at hh
    linarith
  have hn := control_within_limit (by norm_num : (0:ℝ)≤1) hE (by norm_num)
  have hc := clipping_error (e:=a-control x v) hn
  have hid : control x v+(a-control x v)=a := by ring
  rw [hid] at hc
  have hu' : |u-control x v|≤1/10000+1/4000+3/16000 := by
    have hh := abs_add_le (u-saturate 1 a) (saturate 1 a-control x v)
    have hi : u-saturate 1 a+(saturate 1 a-control x v)=u-control x v := by ring
    rw [hi] at hh
    linarith
  constructor
  · apply S03Budget.safe_step hlo hhi hE (D:=1/1250)
    · linarith
    · exact S03Budget.widened_budget
  · have hc' := (S03Range.invariant_ranges hE).2.2
    have hh : |u|≤|u-control x v|+|control x v| := by
      simpa using abs_add_le (u-control x v) (control x v)
    linarith
end S03Decimal
#print axioms S03Decimal.decoded_dot
#print axioms S03Decimal.stale_identity
#print axioms S03Decimal.stale_bound
#print axioms S03Decimal.age_allowance
#print axioms S03Decimal.decimal_step
