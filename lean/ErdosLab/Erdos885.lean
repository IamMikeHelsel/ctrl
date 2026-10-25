import Challenge.Erdos885

open Erdos885

namespace Challenge.Erdos885

theorem solution : statement := by
  refine ⟨{65984625, 508032000, 1578963456}, by simp, by decide, ?_⟩
  have hsub : (↑({5040, 27720, 68880} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({65984625, 508032000, 1578963456} : Finset ℕ),
        factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n (rfl | rfl | rfl) <;> rcases hd with rfl | rfl | rfl
    exacts [mem_factorDifferenceSet_of_eq (b := 5985) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 2205) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 945) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 20160) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 12600) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 6720) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 37296) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 28224) (by norm_num),
      mem_factorDifferenceSet_of_eq (b := 18144) (by norm_num)]
  have hfin : (⋂ n ∈ ({65984625, 508032000, 1578963456} : Finset ℕ),
      factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ 65984625)).subset
      (Set.iInter₂_subset 65984625 (by simp))
  calc 3 = (↑({5040, 27720, 68880} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end Challenge.Erdos885
