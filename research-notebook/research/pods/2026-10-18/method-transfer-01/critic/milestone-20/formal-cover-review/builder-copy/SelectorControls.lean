import UniversalSelector
set_option maxHeartbeats 4000000
namespace E10.Controls
open Erdos128.FiniteProfileBridge

def c0 : ℚ := 133/160
def j0 : ℚ := 71/1880
def r0 : ℚ := 1/40
def l1 : ℚ := (j0-r0)/(1/(2*c0)-1/2)-2*meanDegree (1/(2*c0)) j0

theorem obstruction_identity (L : ℚ) :
 highCertificate (1/(2*c0)) j0 r0 L = 1255919/50895360000+(L-l1)^2/4 := by
 simp only [l1,highCertificate,meanDegree,c0,j0,r0]
 ring

theorem obstruction_all_slopes (L : ℚ) : 0 < highCertificate (1/(2*c0)) j0 r0 L := by
 rw [obstruction_identity]
 have hs := sq_nonneg (L-l1)
 linarith

def AtTarget (r c j : ℚ) : Prop := c^2*j ≤ r ∨
 (3/4 ≤ c ∧ completion c+I-j ≤ r) ∨
 (c<1 ∧ ∃ L : ℚ, lowCertificate (1/(2*c)) j r L ≤ 0 ∧ highCertificate (1/(2*c)) j r L ≤ 0)

theorem wrong_target_counterexample :
 1/2 ≤ c0 ∧ c0 ≤ 1 ∧ 0 ≤ j0 ∧ j0 ≤ I ∧ ¬ AtTarget r0 c0 j0 := by
 refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
 intro h
 rcases h with h | h | ⟨_,L,_,hH⟩
 · have : ¬ c0^2*j0 ≤ r0 := by decide +kernel
   exact this h
 · have : ¬ completion c0+I-j0 ≤ r0 := by decide +kernel
   exact this h.2
 · exact (not_le_of_gt (obstruction_all_slopes L)) hH

def cm : ℚ := 5347/6400
def jm : ℚ := 895/24064

theorem matched_slope_needed :
 R < cm^2*jm ∧ R < completion cm+I-jm ∧
 0 < highCertificate (1/(2*cm)) jm R (Expr.slope cm jm 0) ∧
 lowCertificate (1/(2*cm)) jm R (Expr.slope cm jm 1) < 0 ∧
 highCertificate (1/(2*cm)) jm R (Expr.slope cm jm 1) < 0 := by decide +kernel

theorem square_crossing_zero : (sq (-1,2)).1 = 0 ∧ Mem (0^2) (sq (-1,2)) := by unfold Mem; decide +kernel

theorem reciprocal_reversal : inv (1,2) = (1/2,1) ∧ Mem (1/(2:ℚ)) (inv (1,2)) := by unfold Mem; decide +kernel

theorem varying_slope_no_cancellation :
 ((-1:ℚ)*(1/4-1/2)+(1:ℚ)*(3/4-1/2))/2 = 1/4 := by norm_num

theorem closed_split_boundary : Mem (1/2:ℚ) (0,1/2) ∧ Mem (1/2:ℚ) (1/2,1) := by unfold Mem; decide +kernel

theorem missing_child_witness : Mem (3/4:ℚ) (0,1) ∧ ¬ Mem (3/4:ℚ) (0,1/2) := by unfold Mem; decide +kernel

theorem strict_children_miss_boundary :
 Mem (1/2:ℚ) (0,1) ∧ ¬ ((1/2:ℚ)<1/2 ∨ (1/2:ℚ)<1/2) := by unfold Mem; decide +kernel

theorem full_domain_corners : Selected (1/2) 0 ∧ Selected (1/2) I ∧ Selected 1 0 ∧ Selected 1 I := by
 refine ⟨?_,?_,?_,?_⟩ <;> apply universal_selector <;> norm_num [I]

theorem completion_join : Q (3/8) = 3/128 ∧ ((3/8:ℚ)*(1/2-3/8)/2)=3/128 := by decide +kernel

theorem middle_positive_denominators {c : ℚ} (hc : 767/1000 ≤ c) (hu : c ≤ 22/25) :
 0 < c ∧ 0 < 1/(2*c)-1/2 ∧ 0 < 4*R+1 := by
 have hp : 0 < 2*c := by linarith
 have hh : 1/2 < 1/(2*c) := (lt_div_iff₀ hp).2 (by linarith)
 exact ⟨by linarith,by linarith,by norm_num [R]⟩
end E10.Controls
