import FormalConjectures.ErdosProblems.«885»

/-!
# Erdős 885: square-sum grids found by the ctrl pod (AI-generated, 2026-10-18)

Each theorem is one integer reading of a rational grid `U + V ⊆ squares`.
-/

open Erdos885 Set Finset

/-- 3 integers whose factor-difference sets share 6 elements. -/
theorem grid3_three_share_six :
    (↑({7142490, 14215590, 18055770, 36195030, 115690710, 130085034} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({70221547596375, 218508790732375, 2492797287180375} : Finset ℕ), factorDifferenceSet n ∧
    6 ≤ (⋂ n ∈ ({70221547596375, 218508790732375, 2492797287180375} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({7142490, 14215590, 18055770, 36195030, 115690710, 130085034} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({70221547596375, 218508790732375, 2492797287180375} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 5537835) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3880485) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 3289755) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1845945) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 603825) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 537591) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 11636075) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 9294325) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 8292955) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 5269745) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1858865) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1658591) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 46484235) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 43323525) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 41709675) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 35009145) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 18567225) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 16953375) (by norm_num)]
  have hfin : (⋂ n ∈ ({70221547596375, 218508790732375, 2492797287180375} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 70221547596375)).subset
      (Set.iInter₂_subset 70221547596375 (by simp))
  refine ⟨hsub, ?_⟩
  calc 6 = (↑({7142490, 14215590, 18055770, 36195030, 115690710, 130085034} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid3_three_share_six

/-- 5 integers whose factor-difference sets share 4 elements. -/
theorem grid3_five_share_four :
    (↑({3571245, 9109080, 15207320, 50055480} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({9441739728000, 17187229180800, 78691564581300, 833332826056500, 1054443806711316} : Finset ℕ), factorDifferenceSet n ∧
    4 ≤ (⋂ n ∈ ({9441739728000, 17187229180800, 78691564581300, 833332826056500, 1054443806711316} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({3571245, 9109080, 15207320, 50055480} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({9441739728000, 17187229180800, 78691564581300, 833332826056500, 1054443806711316} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 1768275) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 939600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 597400) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 187920) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2728320) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1604280) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1056760) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 341040) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 7263135) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 5417190) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 4079970) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 1525590) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 27137055) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 24670050) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 22248450) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 13178550) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 30735636) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 28235514) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 25746894) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 15970206) (by norm_num)]
  have hfin : (⋂ n ∈ ({9441739728000, 17187229180800, 78691564581300, 833332826056500, 1054443806711316} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 9441739728000)).subset
      (Set.iInter₂_subset 9441739728000 (by simp))
  refine ⟨hsub, ?_⟩
  calc 4 = (↑({3571245, 9109080, 15207320, 50055480} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms grid3_five_share_four
