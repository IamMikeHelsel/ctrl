import VacuumProjector

noncomputable section
namespace HyperbolicSpinor

@[simp] theorem word_append (L T : List J) : word (L++T) = word L * word T := by
  simp [word, List.map_append, List.prod_append]

theorem annihilate_word_absent (i : J) (L : List J) (h : i ∉ L) :
    annihilate i (word L) = 0 := by
  induction L with
  | nil => simp
  | cons j L ih =>
    rw [word_cons, annihilate_create]
    have hij : i ≠ j := by simpa using ((show i ≠ j ∧ i ∉ L from by simpa using h)).1
    have hiL : i ∉ L := ((show i ≠ j ∧ i ∉ L from by simpa using h)).2
    simp [hij, ih hiL]

theorem annihilate_word_prefix (i : J) (L T : List J) (h : i ∉ L) :
    annihilate i (word (L++T)) = (-1 : ℝ)^L.length • (word L * annihilate i (word T)) := by
  induction L with
  | nil => simp
  | cons j L ih =>
    have hij : i ≠ j := ((show i ≠ j ∧ i ∉ L from by simpa using h)).1
    have hiL : i ∉ L := ((show i ≠ j ∧ i ∉ L from by simpa using h)).2
    rw [List.cons_append, word_cons, annihilate_create]
    rw [ih hiL]
    simp [hij, word_cons, pow_succ, mul_assoc]

theorem create_word_prefix (i : J) (L T : List J) :
    create i (word (L++T)) = (-1 : ℝ)^L.length • (word L * create i (word T)) := by
  induction L with
  | nil => simp
  | cons j L ih =>
    rw [List.cons_append, word_cons, create_swap, ih]
    simp [word_cons, pow_succ, mul_assoc]

/-- The sign is the number of preceding generators. -/
theorem annihilate_word_hit (i : J) (L T : List J) (hL : i ∉ L) (hT : i ∉ T) :
    annihilate i (word (L++i::T)) = (-1 : ℝ)^L.length • word (L++T) := by
  rw [annihilate_word_prefix i L (i::T) hL, word_cons, annihilate_create,
    annihilate_word_absent i T hT]
  simp

theorem create_word_insert (i : J) (L T : List J) :
    create i (word (L++T)) = (-1 : ℝ)^L.length • word (L++i::T) := by
  rw [create_word_prefix]
  simp

theorem create_word_present (i : J) (L : List J) (h : i ∈ L) :
    create i (word L) = 0 := by
  obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp h
  rw [create_word_prefix, word_cons, create_square]
  simp

@[simp] theorem ordered_nodup (T : Finset J) : (ordered T).Nodup :=
  List.nodup_ofFn_ofInjective (T.orderEmbOfFin rfl).injective

theorem annihilate_basis_absent (i : J) (T : Finset J) (h : i ∉ T) :
    annihilate i (spinBasis T) = 0 := by
  rw [basis_word]
  exact annihilate_word_absent i _ (by simpa using h)

theorem create_basis_present (i : J) (T : Finset J) (h : i ∈ T) :
    create i (spinBasis T) = 0 := by
  rw [basis_word]
  exact create_word_present i _ (by simpa using h)

/-- This formula covers every occupied coordinate of every actual subset basis vector. -/
theorem annihilate_basis_present (i : J) (T : Finset J) (h : i ∈ T) :
    ∃ A B : List J, ordered T = A++i::B ∧ i ∉ A ∧ i ∉ B ∧
      annihilate i (spinBasis T) = (-1 : ℝ)^A.length • word (A++B) := by
  obtain ⟨A, B, hs⟩ := List.mem_iff_append.mp ((mem_ordered i T).mpr h)
  have hn := ordered_nodup T
  rw [hs] at hn
  have hA : i ∉ A := by
    intro hi
    exact (List.nodup_append.mp hn).2.2 i hi i (by simp) rfl
  have hB : i ∉ B := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  refine ⟨A, B, hs, hA, hB, ?_⟩
  rw [basis_word, hs, annihilate_word_hit i A B hA hB]

end HyperbolicSpinor
