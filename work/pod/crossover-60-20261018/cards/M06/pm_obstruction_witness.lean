import Mathlib.Tactic
namespace CampaignM06Witness
def edges : List (Nat × Nat) := [(0,1),(0,4),(0,6),(0,9),(0,12),(0,15),(0,17),(0,20),(1,2),(1,5),(1,7),(1,11),(1,13),(1,16),(1,18),(2,3),(2,6),(2,8),(2,12),(2,14),(2,17),(2,19),(3,4),(3,7),(3,9),(3,13),(3,15),(3,18),(3,20),(4,5),(4,8),(4,11),(4,14),(4,16),(4,19),(5,10),(5,12),(5,15),(5,21),(6,10),(6,11),(6,13),(6,21),(7,10),(7,12),(7,14),(7,21),(8,10),(8,13),(8,15),(8,21),(9,10),(9,11),(9,14),(9,21),(10,16),(10,17),(10,18),(10,19),(10,20),(11,22),(12,22),(13,22),(14,22),(15,22),(16,22),(17,22),(18,22),(19,22),(20,22),(21,22)]
def rows : List Nat := [1217106,338085,676170,1352340,608553,2135058,2108421,2118666,2139156,2116617,2032608,4194898,4194469,4194634,4194964,4194601,4195346,4195333,4195338,4195348,4195337,4195296,4192256]
theorem simple_edges : edges.Nodup ∧ ∀ e ∈ edges, e.1 < e.2 ∧ e.2 < 23 := by decide
theorem no_common_neighbor : ∀ e ∈ edges, (rows[e.1]! &&& rows[e.2]!) = 0 := by decide
theorem explicit_cut : (edges.filter (fun e => (6630565:Nat).testBit e.1 == (6630565:Nat).testBit e.2)).length = 20 := by decide
theorem density_and_target : (8/47:ℚ)<142/529 ∧ (142/529:ℚ)<49/125 ∧ (20:ℚ)<2*23^2/47 := by norm_num
end CampaignM06Witness
#print axioms CampaignM06Witness.simple_edges
#print axioms CampaignM06Witness.no_common_neighbor
#print axioms CampaignM06Witness.explicit_cut
#print axioms CampaignM06Witness.density_and_target
