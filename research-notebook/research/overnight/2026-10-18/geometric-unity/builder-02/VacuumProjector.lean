import FockOperators

noncomputable section
namespace HyperbolicSpinor

/-- Ordered products of actual exterior generators. -/
def word (L : List J) : S7 := (L.map fun j => ExteriorAlgebra.ι ℝ (basisVector j)).prod
@[simp] theorem word_nil : word [] = 1 := rfl
@[simp] theorem word_cons (j : J) (L : List J) : word (j::L) = create j (word L) := rfl

def ordered (T : Finset J) : List J := List.ofFn (T.orderEmbOfFin rfl)

theorem basis_word (T : Finset J) : spinBasis T = word (ordered T) := by
  simp [spinBasis, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    word, ordered, List.map_ofFn, basisVector]

@[simp] theorem mem_ordered (i : J) (T : Finset J) : i ∈ ordered T ↔ i ∈ T := by
  simp only [ordered, List.mem_ofFn]
  exact Set.ext_iff.mp (Finset.range_orderEmbOfFin T rfl) i

@[simp] theorem ordered_eq_nil (T : Finset J) : ordered T = [] ↔ T = ∅ := by
  rw [← List.length_eq_zero_iff]
  simp [ordered]

/-- Annihilation after creation removes words containing this coordinate. -/
theorem emptyFactor_word (i : J) (L : List J) :
    emptyFactor i (word L) = if i ∈ L then 0 else word L := by
  induction L with
  | nil => simp
  | cons j L ih =>
    by_cases h : i=j
    · subst j; simp
    · rw [word_cons, emptyFactor_distinct i j h, ih]
      by_cases hm : i ∈ L <;> simp [h, hm]

def factors (L : List J) : Module.End ℝ S7 := (L.map emptyFactor).prod

@[simp] theorem factors_nil : factors [] = 1 := rfl
@[simp] theorem factors_cons (i : J) (L : List J) : factors (i::L) = emptyFactor i * factors L := rfl

theorem factors_word (L T : List J) :
    factors L (word T) = if ∃ i ∈ L, i ∈ T then 0 else word T := by
  induction L with
  | nil => simp
  | cons i L ih =>
    change emptyFactor i (factors L (word T)) = _
    rw [ih]
    by_cases h : ∃ j ∈ L, j ∈ T
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [emptyFactor_word]
      by_cases hi : i ∈ T <;> simp [h, hi]

def vacuum : Module.End ℝ S7 := factors (List.ofFn (fun i : J => i))

theorem vacuum_word (T : List J) : vacuum (word T) = if T=[] then 1 else 0 := by
  rw [vacuum, factors_word]
  by_cases h : T=[]
  · subst T; simp
  · have hn : ∃ i, i ∈ T := List.ne_nil_iff_exists_mem.mp h
    simp [h, hn]

/-- All 128 actual exterior basis vectors are covered. -/
theorem vacuum_basis (T : Finset J) : vacuum (spinBasis T) = if T=∅ then 1 else 0 := by
  rw [basis_word, vacuum_word]
  simp

@[simp] theorem vacuum_one : vacuum (1 : S7) = 1 := by
  simpa using vacuum_word []

theorem vacuum_nonempty (T : Finset J) (h : T.Nonempty) : vacuum (spinBasis T) = 0 := by
  simp [vacuum_basis, h.ne_empty]

end HyperbolicSpinor
