import Mathlib.Tactic

namespace V06InventorBoundary

/-- Gauge R0=I, all measured rotations -I, directed edges01,12,02 once each. -/
def cost (c s d t : ℝ) : ℝ :=
  2*(21*((c+1)^2+s^2)+12*((c+d)^2+(s+t)^2)+28*((d+1)^2+t^2))

theorem certificate (c s d t : ℝ)
    (h1 : c^2+s^2=1) (h2 : d^2+t^2=1) :
    cost c s d t=96+2*((7+3*c+4*d)^2+(3*s+4*t)^2) := by
  dsimp [cost]
  nlinarith

theorem global_lower_bound (c s d t : ℝ)
    (h1 : c^2+s^2=1) (h2 : d^2+t^2=1) : 96 ≤ cost c s d t := by
  rw [certificate _ _ _ _ h1 h2]
  nlinarith [sq_nonneg (7+3*c+4*d), sq_nonneg (3*s+4*t)]

theorem candidate :
    (-1 : ℝ)^2+0^2=1 ∧ (-1 : ℝ)^2+0^2=1 ∧ cost (-1) 0 (-1) 0=96 := by
  norm_num [cost]

theorem unique_minimizer (c s d t : ℝ)
    (h1 : c^2+s^2=1) (h2 : d^2+t^2=1)
    (hmin : cost c s d t=96) : c = -1 ∧ s = 0 ∧ d = -1 ∧ t = 0 := by
  have hc : -1 ≤ c := by nlinarith [sq_nonneg s, sq_nonneg (c+1)]
  have hd : -1 ≤ d := by nlinarith [sq_nonneg t, sq_nonneg (d+1)]
  rw [certificate _ _ _ _ h1 h2] at hmin
  have hsquare := sq_nonneg (3*s+4*t)
  have hz : 7+3*c+4*d=0 := by nlinarith
  have hc' : c = -1 := by linarith
  have hd' : d = -1 := by linarith
  have hs' : s = 0 := by rw [hc'] at h1; nlinarith [sq_nonneg s]
  have ht' : t = 0 := by rw [hd'] at h2; nlinarith [sq_nonneg t]
  exact ⟨hc',hs',hd',ht'⟩

/-- Scalar slack is a rank-one quadratic form. This algebra alone does not
decide uniqueness; the preceding theorem also uses both circle constraints. -/
theorem rank_one_slack_identity (x y z : ℝ) :
    49*x^2+9*y^2+16*z^2+42*x*y+56*x*z+24*y*z=(7*x+3*y+4*z)^2 := by
  ring

#print axioms certificate
#print axioms global_lower_bound
#print axioms candidate
#print axioms unique_minimizer
#print axioms rank_one_slack_identity
end V06InventorBoundary
