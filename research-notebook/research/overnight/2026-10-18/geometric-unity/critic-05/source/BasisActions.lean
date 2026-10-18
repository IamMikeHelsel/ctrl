import MatrixUnits

noncomputable section
namespace HyperbolicSpinor

theorem ordered_erase_of_split (i : J) (T : Finset J) (A B : List J)
    (hs : ordered T = A++i::B) : ordered (T.erase i) = A++B := by
  have hp := ordered_pairwise T
  rw [hs] at hp
  obtain ⟨hA, hiB, hAB⟩ := List.pairwise_append.mp hp
  have hp' : (A++B).Pairwise (· < ·) :=
    List.pairwise_append.mpr ⟨hA, (List.pairwise_cons.mp hiB).2,
      fun a ha b hb => hAB a ha b (by simp [hb])⟩
  apply (ordered_pairwise (T.erase i)).eq_of_mem_iff hp'
  intro j
  have hm : j ∈ T ↔ j ∈ A++i::B := by rw [← mem_ordered, hs]
  have hn := ordered_nodup T
  rw [hs] at hn
  have hniA : i ∉ A := by
    intro hi
    exact (List.nodup_append.mp hn).2.2 i hi i (by simp) rfl
  have hniB : i ∉ B := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  simp only [mem_ordered, Finset.mem_erase, hm, List.mem_append, List.mem_cons]
  aesop

/-- The contraction sign and resulting actual subset basis vector. -/
theorem annihilate_basis_present_exact (i : J) (T : Finset J) (h : i ∈ T) :
    ∃ A B : List J, ordered T = A++i::B ∧
      annihilate i (spinBasis T) = (-1 : ℝ)^A.length • spinBasis (T.erase i) := by
  obtain ⟨A, B, hs, _, _, hv⟩ := annihilate_basis_present i T h
  refine ⟨A, B, hs, ?_⟩
  rw [basis_word (T.erase i), ordered_erase_of_split i T A B hs]
  exact hv

/-- The insertion sign and resulting actual subset basis vector. -/
theorem create_basis_absent_exact (i : J) (T : Finset J) (h : i ∉ T) :
    ∃ A B : List J, ordered (insert i T) = A++i::B ∧ ordered T = A++B ∧
      create i (spinBasis T) = (-1 : ℝ)^A.length • spinBasis (insert i T) := by
  have hm : i ∈ ordered (insert i T) := (mem_ordered i _).mpr (by simp)
  obtain ⟨A, B, hs⟩ := List.mem_iff_append.mp hm
  have ht : ordered T = A++B := by
    simpa [h] using ordered_erase_of_split i (insert i T) A B hs
  refine ⟨A, B, hs, ht, ?_⟩
  rw [basis_word T, ht, create_word_insert, basis_word (insert i T), hs]

end HyperbolicSpinor
