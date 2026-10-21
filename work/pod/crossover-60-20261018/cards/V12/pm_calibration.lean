import Mathlib.Tactic
namespace V12PM
-- Five independent equations for I,Rx,Ry; actual homography row binding is explicit in notes.
theorem unique_metric (c s b11 b12 b22 b13 b23 b33 : ℝ)
 (hc : c^2+s^2=1) (hs : s≠0) (h12 : b12=0) (hdiag : b11=b22)
 (hx : c*b12+s*b13=0) (hy : c*b12-s*b23=0)
 (hn : b11-c^2*b22-2*c*s*b23-s^2*b33=0) :
 b12=0 ∧ b13=0 ∧ b23=0 ∧ b22=b11 ∧ b33=b11 := by
 have h13 : b13=0 := (mul_eq_zero.mp (show s*b13=0 by simpa [h12] using hx)).resolve_left hs
 have hzero : s*b23=0 := by
  have hh : -(s*b23)=0 := by simpa [h12] using hy
  linarith
 have h23 : b23=0 := (mul_eq_zero.mp hzero).resolve_left hs
 have hc2 := congrArg (fun q : ℝ => q*b11) hc
 have he : s^2*(b11-b33)=0 := by rw [h23] at hn; rw [←hdiag] at hn; nlinarith
 have hd := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hs)
 exact ⟨h12,h13,h23,hdiag.symm,by linarith⟩

def grid (i : Fin 3) : ℚ := if i=0 then -1 else if i=1 then 0 else 1
def c : ℚ := 999999/1000001
def s : ℚ := 2000/1000001
def cp : ℚ := 999991/1000009
def sp : ℚ := 6000/1000009
def f : ℚ := 2999997/999991
-- Input view0 front, view1 rotates aboutx, view2 abouty. These are literal pinhole projections.
def project (cc ss focal depth : ℚ) (view i j : Fin 3) : ℚ × ℚ :=
 let x:=grid i; let y:=grid j
 if view=0 then (320+focal*x/depth,240+focal*y/depth)
 else if view=1 then (320+focal*x/(depth+ss*y),240+focal*cc*y/(depth+ss*y))
 else (320+focal*cc*x/(depth-ss*x),240+focal*y/(depth-ss*x))
theorem proper_angles : c^2+s^2=1 ∧ cp^2+sp^2=1 ∧ f>3 ∧ f*cp*s=sp*c := by norm_num [c,s,cp,sp,f]
theorem positive_depths (i : Fin 3) :
 0<5+s*grid i ∧ 0<5-s*grid i ∧ 0<5*f+sp*grid i ∧ 0<5*f-sp*grid i := by
 fin_cases i <;> norm_num [s,sp,f,grid]
theorem pixel_close (v i j : Fin 3) :
 |(project c s 1000 5 v i j).1-(project cp sp (1000*f) (5*f) v i j).1|≤33/10000 ∧
 |(project c s 1000 5 v i j).2-(project cp sp (1000*f) (5*f) v i j).2|≤33/10000 := by
 fin_cases v <;> fin_cases i <;> fin_cases j <;> norm_num [project,c,s,cp,sp,f,grid]
theorem midpoint_radius (x y : ℝ) (h : |x-y|≤33/10000) :
 |x-(x+y)/2|≤33/20000 ∧ |y-(x+y)/2|≤33/20000 := by
 rw [abs_le] at h
 constructor <;> rw [abs_le] <;> constructor <;> linarith
end V12PM
#print axioms V12PM.unique_metric
#print axioms V12PM.proper_angles
#print axioms V12PM.positive_depths
#print axioms V12PM.pixel_close
#print axioms V12PM.midpoint_radius
