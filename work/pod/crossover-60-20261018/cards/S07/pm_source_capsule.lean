import LeanControls.TravelSafety
import Mathlib.Tactic
noncomputable section
namespace CampaignS07Capsule
open LeanControls LeanControls.SaturatedLag
open LeanControls.TravelSafety

def lift (z : State) (d : ℝ) : State := ![z 0+d,z 1-d,z 2+d]
def Capsule (z : State) : Prop := ∃ c d, V c ≤ 12 ∧ |d|≤1/25 ∧ z=lift c d

theorem input_lift (z : State) (d : ℝ) : input (lift z d)=input z := by
 simp [input,lift]; ring

theorem segment_lift (t : ℝ) (z : State) (w d : ℝ) :
 segment t (lift z d) w = lift (segment t z w) (d*Real.exp (-t)) := by
 unfold SaturatedLag.segment
 rw [input_lift]
 ext i
 fin_cases i <;> simp [lift,heldSegment,heldPosition,heldVelocity,heldAcceleration] <;> ring

theorem hidden_contract (d t : ℝ) (hd : |d|≤1/25) (ht : 0≤t) : |d*Real.exp (-t)|≤1/25 := by
 rw [abs_mul,abs_of_pos (Real.exp_pos _)]
 have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
 calc |d| * Real.exp (-t) ≤ (1/25)*1 := mul_le_mul hd he (le_of_lt (Real.exp_pos _)) (by norm_num)
      _ = 1/25 := by ring

theorem capsule_segment {z : State} {t w : ℝ} (hz : Capsule z)
 (ht : 0≤t) (hthi : t≤1/5) (hw : |w|≤1/100) : Capsule (segment t z w) := by
 obtain ⟨c,d,hc,hd,rfl⟩ := hz
 refine ⟨segment t c w,d*Real.exp (-t),segment_invariant ht hthi hw hc,hidden_contract d t hd ht,segment_lift t c w d⟩

theorem capsule_samples (h w : ℕ→ℝ) (z : State) (hz : Capsule z)
 (hlo : ∀ n,0≤h n) (hhi : ∀ n,h n≤1/5) (hw : ∀ n,|w n|≤1/100) :
 ∀ n, Capsule (samples h w z n) := by
 intro n
 induction n with
 | zero => exact hz
 | succ n ih => exact capsule_segment ih (hlo n) (hhi n) (hw n)

theorem capsule_state (h w : ℕ→ℝ) (z : State) {hmin : ℝ}
 (hmin0 : 0<hmin) (hlo : ∀ n,hmin≤h n) (hhi : ∀ n,h n≤1/5)
 (hw : ∀ n,|w n|≤1/100) (hz : Capsule z) {t : ℝ} (ht : 0≤t) :
 Capsule (state h w z t) := by
 obtain ⟨htlo,hthi⟩ := SamplingClock.segmentIndex_spec h hmin0 hlo ht
 rw [SamplingClock.sampleTime_succ] at hthi
 apply capsule_segment (capsule_samples h w z hz (fun n => hmin0.le.trans (hlo n)) hhi hw _)
   (sub_nonneg.mpr htlo) (by linarith [hhi (SamplingClock.segmentIndex h t)])
   (hw (SamplingClock.segmentIndex h t))

theorem original_subset {z : State} (hz : V z≤12) : Capsule z := by
 refine ⟨z,0,hz,by norm_num,?_⟩
 ext i; fin_cases i <;> simp [lift]
end CampaignS07Capsule
#print axioms CampaignS07Capsule.input_lift
#print axioms CampaignS07Capsule.segment_lift
#print axioms CampaignS07Capsule.hidden_contract
#print axioms CampaignS07Capsule.capsule_segment
#print axioms CampaignS07Capsule.capsule_samples
#print axioms CampaignS07Capsule.capsule_state
#print axioms CampaignS07Capsule.original_subset
