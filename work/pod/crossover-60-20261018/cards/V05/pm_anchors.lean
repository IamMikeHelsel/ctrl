import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
noncomputable section
namespace V05Anchors
abbrev V := EuclideanSpace ℝ (Fin 3)
def b1 : V := WithLp.toLp 2 ![1,0,0]
def b2 : V := WithLp.toLp 2 ![0,1,0]
def b3 : V := WithLp.toLp 2 ![0,0,2]
lemma squared_distance (x y : V) : dist x y ^2 =
    (x 0-y 0)^2+(x 1-y 1)^2+(x 2-y 2)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, PiLp.sub_apply]
  ring
/-- Four exact anchor matches identify any Euclidean isometry, including improper ones.
This does not establish measurement truth or an outlier-free acquisition. -/
theorem four_anchors_identify (T : V → V) (hT : Isometry T)
    (h0 : T 0=0) (h1 : T b1=b1) (h2 : T b2=b2) (h3 : T b3=b3) :
    T=id := by
  funext x
  have z := congrArg (fun r : ℝ => r^2) (hT.dist_eq x 0)
  have a := congrArg (fun r : ℝ => r^2) (hT.dist_eq x b1)
  have b := congrArg (fun r : ℝ => r^2) (hT.dist_eq x b2)
  have c := congrArg (fun r : ℝ => r^2) (hT.dist_eq x b3)
  rw [h0] at z
  rw [h1] at a
  rw [h2] at b
  rw [h3] at c
  simp only [squared_distance] at z a b c
  norm_num at z
  change (T x 0)^2+(T x 1)^2+(T x 2)^2=(x 0)^2+(x 1)^2+(x 2)^2 at z
  change (T x 0-1)^2+(T x 1-0)^2+(T x 2-0)^2=(x 0-1)^2+(x 1-0)^2+(x 2-0)^2 at a
  change (T x 0-0)^2+(T x 1-1)^2+(T x 2-0)^2=(x 0-0)^2+(x 1-1)^2+(x 2-0)^2 at b
  change (T x 0-0)^2+(T x 1-0)^2+(T x 2-2)^2=(x 0-0)^2+(x 1-0)^2+(x 2-2)^2 at c
  have hzero : T x 0=x 0 := by nlinarith [z,a]
  have hone : T x 1=x 1 := by nlinarith [z,b]
  have htwo : T x 2=x 2 := by nlinarith [z,c]
  ext i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
#print axioms squared_distance
#print axioms four_anchors_identify
end V05Anchors
