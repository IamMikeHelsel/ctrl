import FormalConjectures.ErdosProblems.«885»

/-!
# Erdős 885: square-sum grids found by the ctrl pod (AI-generated, 2026-10-18)

Each theorem is one integer reading of a rational grid `U + V ⊆ squares`.
-/

open Erdos885 Set Finset

/-- 3 integers whose factor-difference sets share 6 elements. -/
theorem grid4 :
    (↑({14280, 26760, 31640, 67368, 100065, 136920} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({381244500, 1117839744, 31512096000} : Finset ℕ), factorDifferenceSet n ∧
    6 ≤ (⋂ n ∈ ({381244500, 1117839744, 31512096000} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({14280, 26760, 31640, 67368, 100065, 136920} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({381244500, 1117839744, 31512096000} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 13650) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 10290) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 9310) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 5250) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3675) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2730) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 27048) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 22632) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 21168) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 13776) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 10143) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 7728) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 170520) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 164640) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 162400) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 147000) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 134400) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 121800) (by norm_num)]
  have hfin : (⋂ n ∈ ({381244500, 1117839744, 31512096000} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 381244500)).subset
      (Set.iInter₂_subset 381244500 (by simp))
  refine ⟨hsub, ?_⟩
  calc 6 = (↑({14280, 26760, 31640, 67368, 100065, 136920} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid4
