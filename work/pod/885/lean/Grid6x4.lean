import FormalConjectures.ErdosProblems.«885»

/-!
# Erdős 885: square-sum grids found by the ctrl pod (AI-generated, 2026-10-18)

Each theorem is one integer reading of a rational grid `U + V ⊆ squares`.
-/

open Erdos885 Set Finset

/-- 3 integers whose factor-difference sets share 6 elements. -/
theorem grid1_three_share_six :
    (↑({6720, 15855, 26880, 45440, 69510, 129290} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({349102656, 1034586000, 4883112000} : Finset ℕ), factorDifferenceSet n ∧
    6 ≤ (⋂ n ∈ ({349102656, 1034586000, 4883112000} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({6720, 15855, 26880, 45440, 69510, 129290} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({349102656, 1034586000, 4883112000} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 15624) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12369) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 9576) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 6696) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 4704) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2646) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 28980) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 25200) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 21420) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 16660) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 7560) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 66600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 62400) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 57720) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 50760) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 43290) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 30550) (by norm_num)]
  have hfin : (⋂ n ∈ ({349102656, 1034586000, 4883112000} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 349102656)).subset
      (Set.iInter₂_subset 349102656 (by simp))
  refine ⟨hsub, ?_⟩
  calc 6 = (↑({6720, 15855, 26880, 45440, 69510, 129290} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid1_three_share_six

/-- 5 integers whose factor-difference sets share 4 elements. -/
theorem grid1_five_share_four :
    (↑({13440, 75936, 129360, 279840} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({206222625, 677376000, 2019635200, 4786481700, 16670745700} : Finset ℕ), factorDifferenceSet n ∧
    4 ≤ (⋂ n ∈ ({206222625, 677376000, 2019635200, 4786481700, 16670745700} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({13440, 75936, 129360, 279840} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({206222625, 677376000, 2019635200, 4786481700, 16670745700} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 9135) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2625) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1575) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 735) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20160) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 8064) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 5040) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2400) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 38720) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20864) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 14080) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 7040) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 62790) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 40950) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 30030) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 16170) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 122570) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 96614) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 79730) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 50470) (by norm_num)]
  have hfin : (⋂ n ∈ ({206222625, 677376000, 2019635200, 4786481700, 16670745700} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 206222625)).subset
      (Set.iInter₂_subset 206222625 (by simp))
  refine ⟨hsub, ?_⟩
  calc 4 = (↑({13440, 75936, 129360, 279840} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid1_five_share_four

/-- 3 integers whose factor-difference sets share 6 elements. -/
theorem grid2_three_share_six :
    (↑({2988, 4356, 5787, 11164, 17046, 23948} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({4148640, 34418880, 300736800} : Finset ℕ), factorDifferenceSet n ∧
    6 ≤ (⋂ n ∈ ({4148640, 34418880, 300736800} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({2988, 4356, 5787, 11164, 17046, 23948} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({4148640, 34418880, 300736800} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 1032) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 804) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 645) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 360) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 240) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 172) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 4560) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 4080) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3648) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2516) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1824) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1360) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 15912) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 15300) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 14688) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12636) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 10800) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 9100) (by norm_num)]
  have hfin : (⋂ n ∈ ({4148640, 34418880, 300736800} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 4148640)).subset
      (Set.iInter₂_subset 4148640 (by simp))
  refine ⟨hsub, ?_⟩
  calc 6 = (↑({2988, 4356, 5787, 11164, 17046, 23948} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid2_three_share_six

/-- 5 integers whose factor-difference sets share 4 elements. -/
theorem grid2_five_share_four :
    (↑({5976, 10104, 24216, 69624} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({10046592, 24561225, 115706752, 281637972, 564578560} : Finset ℕ), factorDifferenceSet n ∧
    4 ≤ (⋂ n ∈ ({10046592, 24561225, 115706752, 281637972, 564578560} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({5976, 10104, 24216, 69624} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({10046592, 24561225, 115706752, 281637972, 564578560} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 1368) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 912) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 408) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 144) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2799) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2025) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 975) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 351) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 8176) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 6832) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 4088) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1624) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 14058) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12474) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 8586) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3834) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20960) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 19240) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 14560) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 7336) (by norm_num)]
  have hfin : (⋂ n ∈ ({10046592, 24561225, 115706752, 281637972, 564578560} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 10046592)).subset
      (Set.iInter₂_subset 10046592 (by simp))
  refine ⟨hsub, ?_⟩
  calc 4 = (↑({5976, 10104, 24216, 69624} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid2_five_share_four
