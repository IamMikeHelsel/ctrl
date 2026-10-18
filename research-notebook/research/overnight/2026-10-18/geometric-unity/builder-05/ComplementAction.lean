import ComplexControls

noncomputable section
open scoped BigOperators
open Matrix
namespace HyperbolicSpinor

/-- Occupied coordinates below the generator. -/
def lowerCount (i : J) (T : Finset J) : ℕ := (T.filter (· < i)).card

theorem prefix_length (i : J) (T : Finset J) (A B : List J)
    (h : ordered T = A ++ i :: B) : A.length = lowerCount i T := by
  have hp := ordered_pairwise T
  rw [h] at hp
  obtain ⟨hA, hB, hAB⟩ := List.pairwise_append.mp hp
  have ha : ordered (T.filter (· < i)) = A := by
    apply (ordered_pairwise _).eq_of_mem_iff hA
    intro j
    simp only [mem_ordered, Finset.mem_filter]
    have hm : j ∈ T ↔ j ∈ A ++ i :: B := by rw [← mem_ordered, h]
    constructor
    · rintro ⟨hjT, hji⟩
      rcases List.mem_append.mp (hm.mp hjT) with hjA | hjB
      · exact hjA
      · rcases List.mem_cons.mp hjB with rfl | hjB
        · exact False.elim (lt_irrefl _ hji)
        · exact False.elim (lt_asymm hji ((List.pairwise_cons.mp hB).1 _ hjB))
    · intro hjA
      exact ⟨hm.mpr (List.mem_append.mpr (Or.inl hjA)), hAB j hjA i (by simp)⟩
  have hl := congrArg List.length ha
  simpa [ordered, lowerCount] using hl.symm

/-- Toggle one occupied coordinate. This is discrete bookkeeping only. -/
def toggle (i : J) (T : Finset J) : Finset J := if i ∈ T then T.erase i else insert i T

def toggleSign (i : J) (T : Finset J) : ℤ :=
  if i ∈ T then -((-1 : ℤ)^lowerCount i T) else (-1 : ℤ)^lowerCount i T

theorem negative_basis (i : J) (T : Finset J) :
    (create i - annihilate i) (spinBasis T) =
      (toggleSign i T : ℝ) • spinBasis (toggle i T) := by
  by_cases hi : i ∈ T
  · obtain ⟨A, B, hs, ha⟩ := annihilate_basis_present_exact i T hi
    simp only [LinearMap.sub_apply, create_basis_present i T hi, ha, zero_sub,
      toggleSign, toggle, hi, ↓reduceIte]
    rw [prefix_length i T A B hs]
    simp
  · obtain ⟨A, B, hs, ht, hc⟩ := create_basis_absent_exact i T hi
    have hn : lowerCount i (insert i T) = lowerCount i T := by
      unfold lowerCount
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hji⟩
        · exact False.elim (lt_irrefl _ hji)
        · exact ⟨hj, hji⟩
      · rintro ⟨hj, hji⟩; exact ⟨Or.inr hj, hji⟩
    simp only [LinearMap.sub_apply, annihilate_basis_absent i T hi, hc, sub_zero,
      toggleSign, toggle, hi, ↓reduceIte]
    rw [prefix_length i (insert i T) A B hs, hn]
    simp

/-- Coordinate vector of the actual exterior basis. -/
def unitCoord (T : Finset J) : (Finset J → ℝ) := Pi.single T 1

theorem repr_basis_coord (T : Finset J) : (spinBasis.repr (spinBasis T) : Finset J → ℝ) = unitCoord T := by
  ext I
  simp [unitCoord, Pi.single_apply, Finsupp.single_apply, eq_comm]

theorem negative_mulVec (i : J) (T : Finset J) :
    negativeMatrix i *ᵥ unitCoord T = (toggleSign i T : ℝ) • unitCoord (toggle i T) := by
  rw [← repr_basis_coord, negativeMatrix_fock]
  simp only [creationMatrix, contractionMatrix, ← map_sub]
  change LinearMap.toMatrix spinBasis spinBasis (create i - annihilate i) *ᵥ _ = _
  rw [LinearMap.toMatrix_mulVec_repr, negative_basis]
  simp only [map_smul, Finsupp.coe_smul, repr_basis_coord]

/-- Discrete action of a fixed ordered generator product; rightmost acts first. -/
def signedToggles : List J → Finset J → ℤ × Finset J
  | [], T => (1,T)
  | i::L, T => let st := signedToggles L T
              (st.1 * toggleSign i st.2, toggle i st.2)

theorem product_mulVec (L : List J) (T : Finset J) :
    (L.map negativeMatrix).prod *ᵥ unitCoord T =
      ((signedToggles L T).1 : ℝ) • unitCoord (signedToggles L T).2 := by
  induction L with
  | nil => simp [signedToggles]
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec, signedToggles]
    rw [← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, negative_mulVec]
    simp [smul_smul]

/-- Sign for the fixed order N0*N1*...*N6. -/
def complementSign (T : Finset J) : ℤ := (-1)^(∑ i ∈ T, (7-i.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem signedToggles_seven : ∀ T : Finset J,
    signedToggles [0,1,2,3,4,5,6] T = (complementSign T, Tᶜ) := by
  decide

theorem K_mulVec_basis (T : Finset J) :
    K *ᵥ unitCoord T = (complementSign T : ℝ) • unitCoord Tᶜ := by
  have h := product_mulVec [0,1,2,3,4,5,6] T
  rw [signedToggles_seven] at h
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, K, mul_assoc] using h

end HyperbolicSpinor
