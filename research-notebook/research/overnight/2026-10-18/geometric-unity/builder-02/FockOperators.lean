import SplitSpinor

noncomputable section
namespace HyperbolicSpinor
open GUClifford
abbrev J := Fin 7

def basisVector (j : J) : W7 := Pi.single j 1
def coordinate (j : J) : Module.Dual ℝ W7 := LinearMap.proj j
def create (j : J) : Module.End ℝ S7 := Algebra.lmul ℝ S7 (ExteriorAlgebra.ι ℝ (basisVector j))
def annihilate (j : J) : Module.End ℝ S7 := CliffordAlgebra.contractLeft (coordinate j)

@[simp] theorem create_apply (j : J) (x : S7) :
    create j x = ExteriorAlgebra.ι ℝ (basisVector j) * x := rfl
@[simp] theorem annihilate_apply (j : J) (x : S7) :
    annihilate j x = CliffordAlgebra.contractLeft (coordinate j) x := rfl
@[simp] theorem coordinate_basis (i j : J) : coordinate i (basisVector j) = if i=j then 1 else 0 := by
  simp [coordinate, basisVector, Pi.single_apply]

@[simp] theorem create_square (j : J) (x : S7) : create j (create j x) = 0 := by
  simp [create_apply, ← mul_assoc]
@[simp] theorem annihilate_square (j : J) (x : S7) : annihilate j (annihilate j x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (coordinate j) x
@[simp] theorem annihilate_vacuum (j : J) : annihilate j (1 : S7) = 0 :=
  CliffordAlgebra.contractLeft_one _ _

theorem annihilate_create (i j : J) (x : S7) :
    annihilate i (create j x) = (if i=j then (1 : ℝ) else 0) • x - create j (annihilate i x) := by
  simp only [create_apply, annihilate_apply, CliffordAlgebra.contractLeft_ι_mul, coordinate_basis]

theorem create_swap (i j : J) (x : S7) : create i (create j x) = -create j (create i x) := by
  simp only [create_apply, ← mul_assoc]
  rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℝ) (basisVector i) (basisVector j))]
  simp only [neg_mul]

def emptyFactor (i : J) : Module.End ℝ S7 := annihilate i * create i

@[simp] theorem emptyFactor_vacuum (i : J) : emptyFactor i (1 : S7) = 1 := by
  change annihilate i (create i 1) = 1
  rw [annihilate_create]
  simp

@[simp] theorem emptyFactor_same (i : J) (x : S7) : emptyFactor i (create i x) = 0 := by
  change annihilate i (create i (create i x)) = 0
  rw [create_square, map_zero]

theorem emptyFactor_distinct (i j : J) (h : i ≠ j) (x : S7) :
    emptyFactor i (create j x) = create j (emptyFactor i x) := by
  change annihilate i (create i (create j x)) = create j (annihilate i (create i x))
  rw [create_swap, map_neg, annihilate_create]
  simp [h]

end HyperbolicSpinor
