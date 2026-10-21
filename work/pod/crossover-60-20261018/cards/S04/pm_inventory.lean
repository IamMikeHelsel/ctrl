import Mathlib
namespace S04Inventory

theorem visible : True := by trivial

  theorem indented : (2 : ℕ) + 2 = 4 := by norm_num

@[simp] theorem attributed : (3 : ℕ) + 3 = 6 := by norm_num

end S04Inventory
#print axioms S04Inventory.visible
#print axioms S04Inventory.indented
#print axioms S04Inventory.attributed
