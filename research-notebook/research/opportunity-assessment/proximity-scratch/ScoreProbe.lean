/- Local exact arithmetic checks only, using installed Lean 4.35.0.
This is not a Proximity candidate replay (its pinned toolchain is 4.32.2).
The inequalities are score barriers, not coding-theory bounds. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 400000
namespace ProximityFeasibility

theorem lower_next_centibit_fails :
    (1073741824 : Nat)^12800 < 2^6816 * 742375425^12800 := by decide

theorem lower_cell_supremum_next_centibit_fails :
    (262144 : Nat)^12800 < 2^6816 * 181244^12800 := by decide

theorem upper_next_centibit_fails :
    2^11612 * (139775 : Nat)^12800 < 262144^12800 := by decide

#print axioms lower_next_centibit_fails
#print axioms lower_cell_supremum_next_centibit_fails
#print axioms upper_next_centibit_fails
end ProximityFeasibility
