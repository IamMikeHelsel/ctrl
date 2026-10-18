import OrderControls
import BasisActions

noncomputable section
open HyperbolicSpinor GUClifford

local instance : CharZero S7 :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℝ S7))

-- This inverse belongs to the actual splitMatrix, not an abstract map of equal dimension.
example (A : Matrix (Finset (Fin 7)) (Finset (Fin 7)) ℝ) :
    splitMatrix (splitMatrixEquiv.symm A) = A :=
  splitMatrixEquiv.apply_symm_apply A

example (x : Cl) : splitMatrixEquiv.symm (splitMatrix x) = x :=
  splitMatrixEquiv.symm_apply_apply x

example (x y : Cl) : splitAction x = splitAction y ↔ x=y :=
  splitAction_injective.eq_iff

example (f : Module.End ℝ S7) : splitAction (preimage f) = f := preimage_image f

-- The non-transposed matrix-unit action includes every input subset T.
example (I J T : Finset (Fin 7)) :
    splitAction (matrixUnitElement I J) (spinBasis T) = if J=T then spinBasis I else 0 := by
  rw [matrixUnit_image, matrixUnit_basis]

-- Check the coordinate interpretation directly; row is the output index.
example (I J r c : Finset (Fin 7)) :
    splitMatrix (matrixUnitElement I J) r c = if J=c then (if I=r then 1 else 0) else 0 := by
  change LinearMap.toMatrix spinBasis spinBasis (splitAction (matrixUnitElement I J)) r c = _
  rw [LinearMap.toMatrix_apply, matrixUnit_image, matrixUnit_basis]
  by_cases h : J=c <;> simp [h, Finsupp.single_apply]

example (I J K T : Finset (Fin 7)) :
    matrixUnitElement I J * matrixUnitElement K T =
      if J=K then matrixUnitElement I T else 0 := by
  apply splitAction_injective
  rw [map_mul]
  simp only [matrixUnit_image]
  apply spinBasis.ext
  intro U
  by_cases h : J=K <;> by_cases hu : T=U <;>
    simp [h, hu, Module.End.mul_apply, matrixUnit_basis, matrixUnit_image]

example : vacuumElement = matrixUnitElement ∅ ∅ := by
  have hz : spinBasis (∅ : Finset HyperbolicSpinor.J) = (1 : S7) := by
    rw [basis_word, (ordered_eq_nil ∅).mpr rfl, word_nil]
  apply splitAction_injective
  rw [vacuum_image, matrixUnit_image]
  apply spinBasis.ext
  intro T
  rw [vacuum_basis, matrixUnit_basis]
  by_cases h : T=∅ <;> simp [h, eq_comm, hz]

-- Independent sign tests use nonadjacent indices and actual exterior words.
theorem reviewerInsertion : create 3 (word [0,5]) = (-1 : ℝ) • word [0,3,5] := by
  simpa using create_word_insert 3 [0] [5]

theorem reviewerInsertion_notPositive : create 3 (word [0,5]) ≠ word [0,3,5] := by
  intro h
  rw [reviewerInsertion] at h
  have hh := congrArg (fun x : S7 => vacuum (annihilators [0,3,5] x)) h
  simp only [map_smul] at hh
  have hv : vacuum (annihilators [0,3,5] (word [0,3,5])) = (1 : S7) := by
    simpa using annihilators_vacuum_pairing [0,3,5] [0,3,5] (by decide) (by decide)
  rw [hv] at hh
  norm_num at hh

theorem reviewerErasure : annihilate 3 (word [0,3,5]) = (-1 : ℝ) • word [0,5] := by
  simpa using annihilate_word_hit 3 [0] [5] (by decide) (by decide)

theorem reviewerCorrectOrder : vacuum (annihilators [2,5] (word [2,5])) = (1 : S7) := by
  simpa using annihilators_vacuum_pairing [2,5] [2,5] (by decide) (by decide)

theorem reviewerWrongOrder :
    vacuum ((annihilate 2 * annihilate 5) (word [2,5])) = (-1 : S7) := by
  change vacuum (annihilate 2 (annihilate 5 (word [2,5]))) = -1
  have h : annihilate 5 (word [2,5]) = (-1 : ℝ) • word [2] := by
    simpa using annihilate_word_hit 5 [2] [] (by decide) (by decide)
  rw [h, map_smul, map_smul]
  simp

theorem reviewerWrongOrder_notOne :
    vacuum ((annihilate 2 * annihilate 5) (word [2,5])) ≠ (1 : S7) := by
  rw [reviewerWrongOrder]
  norm_num

theorem reviewerNoHalf :
    splitAction (gamma 2 - gamma 9) (create 2 (1 : S7)) = (2 : ℝ) • (1 : S7) := by
  have hp := gamma_positive_action (2 : HyperbolicSpinor.J)
  have hn := gamma_negative_action (2 : HyperbolicSpinor.J)
  change splitAction (gamma (Fin.castAdd 7 (2 : HyperbolicSpinor.J)) -
    gamma (Fin.addNat (2 : HyperbolicSpinor.J) 7)) (create 2 1) = _
  rw [map_sub, hp, hn]
  simp [LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem reviewerNoHalf_notOne :
    splitAction (gamma 2 - gamma 9) (create 2 (1 : S7)) ≠ (1 : S7) := by
  rw [reviewerNoHalf, two_smul]
  norm_num
