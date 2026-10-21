import FormalConjectures.ErdosProblems.«885»

open Erdos885 Set Finset

theorem erdos_885_level_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨{291985920, 624992256, 1274144256, 80527136256}, by simp, by decide, ?_⟩
  have hsub : (↑({28476, 47376, 80024, 263376} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({291985920, 624992256, 1274144256, 80527136256} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 8004) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 5520) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3496) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1104) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 14532) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 10752) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 7168) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2352) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 24192) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 19152) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 13608) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 4752) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 269892) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 261072) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 246568) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 181152) (by norm_num)]
  have hfin : (⋂ n ∈ ({291985920, 624992256, 1274144256, 80527136256} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 291985920)).subset
      (Set.iInter₂_subset 291985920 (by simp))
  calc 4 = (↑({28476, 47376, 80024, 263376} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms erdos_885_level_4

