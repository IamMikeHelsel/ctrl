import RationalIntervals
import SquareCertificate
set_option maxHeartbeats 4000000
namespace E10
open Erdos128.FiniteProfileBridge
def R : ℚ := 251/10000
def I : ℚ := 2/47
def xval (c : ℚ) := 1-1/(2*c)
def Q (x : ℚ) := if x ≤ 3/8 then 3*x^2/2-5*x/4+9/32 else x*(1/2-x)/2
def completion (c : ℚ) := Q (xval c)
def Selected (c j : ℚ) : Prop := c^2*j ≤ R ∨
 (3/4 ≤ c ∧ completion c+I-j ≤ R) ∨
 (c<1 ∧ ∃ L : ℚ, lowCertificate (1/(2*c)) j R L ≤ 0 ∧ highCertificate (1/(2*c)) j R L ≤ 0)
namespace Expr
abbrev sube (a b : Expr) := plus a (minus b)
abbrev dive (a b : Expr) := times a (recip b)
def ey : Expr := dive (.lit 1) (.times (.lit 2) .c)
def em : Expr := .times (.times (.lit 4) .c) .j
def eb : Expr := sube ey (.lit (1/2))
def eL0 : Expr := sube (.times (.lit (8*R)) (sube ey em)) (.times (.lit 2) em)
def eC : Expr := sube (sube .j (.times (.lit (4*R)) (.square (sube ey em)))) (.square em)
def ea : Expr := dive (sube .j (.lit R)) eb
def eL1 : Expr := sube ea (.times (.lit 2) em)
def eD2 : Expr := .square (sube eL1 eL0)
def eHmin : Expr := sube (.times ea em) (.square em)
def eA (t : ℚ) : Expr := .plus eC (dive (.times (.lit (t^2)) eD2) (.lit (4*(4*R+1))))
def eH (t : ℚ) : Expr := .plus eHmin (dive (.times (.lit ((1-t)^2)) eD2) (.lit 4))
def slope (c j t : ℚ) := val c j eL0+t*(val c j eL1-val c j eL0)
theorem mean_eq (c j : ℚ) (hc : c ≠ 0) : meanDegree (1/(2*c)) j = 4*c*j := by
 unfold meanDegree
 field_simp
 <;> ring
theorem A_eq (c j t : ℚ) (hc : c ≠ 0) :
 val c j (eA t) = lowCertificate (1/(2*c)) j R (slope c j t) := by
 unfold lowCertificate lowCenter baseSlope
 rw [mean_eq c j hc]
 simp only [eA,eC,eD2,eL1,ea,eb,ey,em,eL0,sube,dive,val,slope]
 ring
theorem H_eq (c j t : ℚ) (hc : c ≠ 0) :
 val c j (eH t) = highCertificate (1/(2*c)) j R (slope c j t) := by
 unfold highCertificate
 rw [mean_eq c j hc]
 simp only [eH,eHmin,eD2,eL1,ea,eb,ey,em,eL0,sube,dive,val,slope]
 ring
end Expr

theorem x_bounds {c : ℚ} (hc : 3/4 ≤ c) (hu : c ≤ 1) : 1/3 ≤ xval c ∧ xval c ≤ 1/2 := by
 have hp : 0 < 2*c := by linarith
 unfold xval
 have h1 : 1/(2*c) ≤ 2/3 := by apply (div_le_iff₀ hp).2; linarith
 have h2 : 1/2 ≤ 1/(2*c) := by apply (le_div_iff₀ hp).2; linarith
 constructor <;> linarith

theorem x_mono {c d : ℚ} (hc : 0 < c) (hcd : c ≤ d) : xval c ≤ xval d := by
 have h := one_div_le_one_div_of_le (show 0 < 2*c by linarith) (show 2*c ≤ 2*d by linarith)
 unfold xval
 linarith

theorem Q_antitone {x z : ℚ} (hx : 1/3 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1/2) : Q z ≤ Q x := by
 unfold Q
 split_ifs with h1 h2 h2
 · have hh : 0 ≤ (z-x)*(5/4-3*(x+z)/2) := mul_nonneg (by linarith) (by linarith)
   nlinarith
 · linarith
 · have hh1 : 0 ≤ (3/8-x)*(5/4-3*(x+3/8)/2) := mul_nonneg (by linarith) (by linarith)
   have hh2 : 0 ≤ (z-3/8)*(z+3/8-1/2)/2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
   nlinarith
 · have hh : 0 ≤ (z-x)*(x+z-1/2)/2 := div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
   nlinarith

theorem completion_antitone {c d : ℚ} (hc : 3/4 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) : completion d ≤ completion c := by
 exact Q_antitone (x_bounds hc (hcd.trans hd)).1 (x_mono (by linarith) hcd) (x_bounds (hc.trans hcd) hd).2

def momentOK (cb jb : IV) (t : ℚ) : Bool :=
 decide (0 < cb.1 ∧ cb.2 < 1) && Expr.safe cb jb (Expr.eA t) && Expr.safe cb jb (Expr.eH t) &&
 decide ((Expr.box cb jb (Expr.eA t)).2 ≤ 0 ∧ (Expr.box cb jb (Expr.eH t)).2 ≤ 0)
theorem moment_sound {cb jb : IV} {c j t : ℚ} (hc : Mem c cb) (hj : Mem j jb)
 (hok : momentOK cb jb t = true) : Selected c j := by
 simp only [momentOK, Bool.and_eq_true_iff, decide_eq_true_eq] at hok
 rcases hok with ⟨⟨⟨⟨hp,hu⟩,ha⟩,hh⟩,hA,hH⟩
 have hca : c ≠ 0 := ne_of_gt (hp.trans_le hc.1)
 have h1 := (Expr.sound (Expr.eA t) hc hj ha).2.trans hA
 have h2 := (Expr.sound (Expr.eH t) hc hj hh).2.trans hH
 rw [Expr.A_eq c j t hca] at h1
 rw [Expr.H_eq c j t hca] at h2
 exact Or.inr (Or.inr ⟨hc.2.trans_lt hu, Expr.slope c j t, h1,h2⟩)

theorem uniform_sound {cb jb : IV} {c j : ℚ} (hc : Mem c cb) (hj : Mem j jb)
 (hp : 0 ≤ cb.1) (hjp : 0 ≤ jb.1) (h : cb.2^2*jb.2 ≤ R) : Selected c j := by
 have hcs : c^2 ≤ cb.2^2 := by nlinarith [hc.1,hc.2]
 have hjs : 0 ≤ j := hjp.trans hj.1
 exact Or.inl ((mul_le_mul hcs hj.2 hjs (sq_nonneg _)).trans h)

theorem completion_sound {cb jb : IV} {c j : ℚ} (hc : Mem c cb) (hj : Mem j jb)
 (hp : 3/4 ≤ cb.1) (hu : cb.2 ≤ 1) (h : completion cb.1+I-jb.1 ≤ R) : Selected c j := by
 have hq := completion_antitone hp hc.1 (hc.2.trans hu)
 exact Or.inr (Or.inl ⟨hp.trans hc.1,by linarith [hj.1]⟩)

def Covered (cb jb : IV) : Prop := ∀ c j : ℚ, Mem c cb → Mem j jb → Selected c j

theorem split_c (lo hi jl jh mid : ℚ)
 (hl : Covered (lo,mid) (jl,jh)) (hr : Covered (mid,hi) (jl,jh)) : Covered (lo,hi) (jl,jh) := by
 intro c j hc hj
 by_cases h : c ≤ mid
 · exact hl c j ⟨hc.1,h⟩ hj
 · exact hr c j ⟨le_of_not_ge h,hc.2⟩ hj

theorem split_j (lo hi jl jh mid : ℚ)
 (hl : Covered (lo,hi) (jl,mid)) (hr : Covered (lo,hi) (mid,jh)) : Covered (lo,hi) (jl,jh) := by
 intro c j hc hj
 by_cases h : j ≤ mid
 · exact hl c j hc ⟨hj.1,h⟩
 · exact hr c j hc ⟨le_of_not_ge h,hj.2⟩
end E10
