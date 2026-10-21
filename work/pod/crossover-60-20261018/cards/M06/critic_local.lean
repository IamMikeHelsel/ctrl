import Mathlib.Tactic
namespace CampaignM06Critic

def cubeEdges : List (Nat × Nat) :=
  [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]

def crossing (s : Finset Nat) : Nat :=
  (cubeEdges.filter fun e => decide (e.1 ∈ s) != decide (e.2 ∈ s)).length

theorem cube_cut_counts : crossing {1,2,5,6} = 8 ∧ crossing {1,2,4,7} = 12 := by decide

theorem bad_normalized_cost : (4/64:ℚ) > 2/47 ∧ (24/64:ℚ) > 8/47 ∧
    (24/64:ℚ) < 49/125 := by norm_num

/-- Conditional gain algebra; the graph/blow-up gain identity is supplied separately. -/
theorem finite_radius_obstruction (t s gain : ℤ) (hs : 0 ≤ s) (hst : s ≤ t+1)
    (hg : gain ≤ -t*s+s*(s-1)) : gain ≤ 0 := by
  have h : 0 ≤ s*(t+1-s) := mul_nonneg hs (by omega)
  nlinarith

theorem strict_finite_radius (t s gain : ℤ) (hs : 0 < s) (hst : s ≤ t)
    (hg : gain ≤ -t*s+s*(s-1)) : gain < 0 := by
  have h : 0 ≤ s*(t-s) := mul_nonneg (le_of_lt hs) (by omega)
  nlinarith
end CampaignM06Critic
#print axioms CampaignM06Critic.cube_cut_counts
#print axioms CampaignM06Critic.bad_normalized_cost
#print axioms CampaignM06Critic.finite_radius_obstruction
#print axioms CampaignM06Critic.strict_finite_radius
