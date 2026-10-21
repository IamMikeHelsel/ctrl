import Mathlib.Tactic
namespace CampaignM06Code
def labels : List Nat := [0, 3, 5, 6, 9, 10, 12, 15, 17, 18, 20, 23, 24, 27, 29, 30]
def edges : List (Nat × Nat) := [(0, 7), (0, 11), (0, 13), (0, 14), (0, 15), (1, 6), (1, 10), (1, 12), (1, 14), (1, 15), (2, 5), (2, 9), (2, 12), (2, 13), (2, 15), (3, 4), (3, 8), (3, 12), (3, 13), (3, 14), (4, 9), (4, 10), (4, 11), (4, 15), (5, 8), (5, 10), (5, 11), (5, 14), (6, 8), (6, 9), (6, 11), (6, 13), (7, 8), (7, 9), (7, 10), (7, 12), (8, 15), (9, 14), (10, 13), (11, 12)]
def agreement (u v : Nat) : Nat :=
  ((List.range 5).filter fun k => (labels[u]!).testBit k == (labels[v]!).testBit k).length
 theorem every_edge : ∀ e ∈ edges, agreement e.1 e.2 = 1 := by decide
 theorem graph_size : edges.length = 40 ∧ labels.length = 16 := by decide
 theorem average_cut (a b c d e m : ℝ) (h : a+b+c+d+e=m) :
  a≤m/5 ∨ b≤m/5 ∨ c≤m/5 ∨ d≤m/5 ∨ e≤m/5 := by
  by_contra hn
  push_neg at hn
  rcases hn with ⟨ha,hb,hc,hd,he⟩
  linarith
 theorem density_gate (m N : ℝ) (h : 2*m≤(20/47)*N) : m/5≤(2/47)*N := by linarith
 theorem middle_covered : (49/125:ℝ) < 20/47 := by norm_num
 theorem clebsch_local_failure : (11/256:ℝ)>2/47 ∧ (8/256:ℝ)<2/47 := by norm_num
 theorem locality_failure (t : ℝ) (ht : 0<t) : 4*t^2 > (2/47)*(8*t)^2 := by nlinarith [sq_pos_of_pos ht]
end CampaignM06Code
#print axioms CampaignM06Code.every_edge
#print axioms CampaignM06Code.graph_size
#print axioms CampaignM06Code.average_cut
#print axioms CampaignM06Code.density_gate
#print axioms CampaignM06Code.middle_covered
#print axioms CampaignM06Code.clebsch_local_failure
#print axioms CampaignM06Code.locality_failure
