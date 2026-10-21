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

-- Sharp source-position certificate copied verbatim from critic_source_position.lean.
noncomputable section
namespace S07CriticPosition
open LeanControls Matrix
/-- Sharp position support bound binds the literal source energy/P, not a renamed quadratic. -/
theorem sharp_position (z : SaturatedLag.State) :
    (z 0)^2 ≤ (3550075/11131832:ℝ)*TravelSafety.V z := by
  have he : (3550075/11131832:ℝ)*TravelSafety.V z-(z 0)^2 =
    (7924369/5565916:ℝ)*(z 0+(36494771/15848738:ℝ)*z 1+(17750375/15848738:ℝ)*z 2)^2+
    (38095377836923/44106372207004:ℝ)*(z 1+(46767/32758:ℝ)*z 2)^2 := by
    simp [TravelSafety.V, BernsteinCertificate.energy, TravelSafety.P,
      Generated.TravelQuarterLower.P, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  have h0 : 0≤(7924369/5565916:ℝ)*(z 0+(36494771/15848738:ℝ)*z 1+(17750375/15848738:ℝ)*z 2)^2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0≤(38095377836923/44106372207004:ℝ)*(z 1+(46767/32758:ℝ)*z 2)^2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem core_position {z : SaturatedLag.State} (hz : TravelSafety.V z≤11) : |z 0|≤15/8 := by
  have hp := sharp_position z
  have hbudget : (3550075/11131832:ℝ)*11≤(15/8)^2 := by norm_num
  have hbound : (z 0)^2≤(15/8:ℝ)^2 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z 0-15/8),sq_nonneg (z 0+15/8)]
theorem core_position_twelve {z : SaturatedLag.State} (hz : TravelSafety.V z≤12) : |z 0|≤49/25 := by
  have hp := sharp_position z
  have hbudget : (3550075/11131832:ℝ)*12≤(49/25)^2 := by norm_num
  have hbound : (z 0)^2≤(49/25:ℝ)^2 := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z 0-49/25),sq_nonneg (z 0+49/25)]
end S07CriticPosition
#print axioms S07CriticPosition.sharp_position
#print axioms S07CriticPosition.core_position

#print axioms S07CriticPosition.core_position_twelve
namespace CampaignS07Capsule
open LeanControls LeanControls.SaturatedLag LeanControls.TravelSafety

theorem capsule_position {z : State} (hz : Capsule z) : |z 0|≤2 := by
 obtain ⟨c,d,hc,hd,rfl⟩ := hz
 have hpos := S07CriticPosition.core_position_twelve hc
 have htri := abs_add_le (c 0) d
 simp only [lift,Matrix.cons_val_zero]
 linarith

theorem capsule_travel (h w : ℕ→ℝ) (z : State) {hmin : ℝ}
 (hmin0 : 0<hmin) (hlo : ∀ n,hmin≤h n) (hhi : ∀ n,h n≤1/5)
 (hw : ∀ n,|w n|≤1/100) (hz : Capsule z) {t : ℝ} (ht : 0≤t) :
 |state h w z t 0|≤2 := capsule_position (capsule_state h w z hmin0 hlo hhi hw hz ht)

theorem strict_extra : Capsule ![(91/50:ℝ),-(91/50),91/50] ∧
 V ![(91/50:ℝ),-(91/50),91/50]>12 := by
 constructor
 · refine ⟨![(89/50:ℝ),-(89/50),89/50],1/25,?_,by norm_num,?_⟩
   · norm_num [V,BernsteinCertificate.energy,TravelSafety.P,Generated.TravelQuarterLower.P,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
   · ext i; fin_cases i <;> norm_num [lift]
 · norm_num [V,BernsteinCertificate.energy,TravelSafety.P,Generated.TravelQuarterLower.P,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
end CampaignS07Capsule
#print axioms CampaignS07Capsule.capsule_position
#print axioms CampaignS07Capsule.capsule_travel
#print axioms CampaignS07Capsule.strict_extra
