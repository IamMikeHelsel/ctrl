import WordActions
import FockImage

noncomputable section
namespace HyperbolicSpinor
open GUClifford

def annihilators (L : List J) : Module.End ℝ S7 := (L.reverse.map annihilate).prod
@[simp] theorem annihilators_nil : annihilators [] = 1 := rfl
@[simp] theorem annihilators_cons (j : J) (L : List J) :
    annihilators (j::L) = annihilators L * annihilate j := by
  simp [annihilators]

theorem vacuum_create (j : J) (x : S7) : vacuum (create j x) = 0 := by
  have he : vacuum * create j = (0 : Module.End ℝ S7) := by
    apply spinBasis.ext
    intro T
    change vacuum (create j (spinBasis T)) = 0
    rw [basis_word, ← word_cons, vacuum_word]
    simp
  exact congrArg (fun f : Module.End ℝ S7 => f x) he

theorem annihilators_create_absent (j : J) (L : List J) (h : j ∉ L) (x : S7) :
    annihilators L (create j x) = (-1 : ℝ)^L.length • create j (annihilators L x) := by
  induction L generalizing x with
  | nil => simp
  | cons i L ih =>
    have hji : j ≠ i := ((show j ≠ i ∧ j ∉ L from by simpa using h)).1
    have hjL : j ∉ L := ((show j ≠ i ∧ j ∉ L from by simpa using h)).2
    rw [annihilators_cons]
    change annihilators L (annihilate i (create j x)) = _
    rw [annihilate_create]
    simp only [hji.symm, ↓reduceIte, zero_smul, zero_sub, map_neg]
    rw [ih hjL]
    simp [pow_succ]

theorem ordered_pairwise (T : Finset J) : (ordered T).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j h
  exact (T.orderEmbOfFin rfl).strictMono h

/-- Reversed contraction order gives the positive Kronecker pairing. -/
theorem annihilators_vacuum_pairing (L T : List J)
    (hL : L.Pairwise (· < ·)) (hT : T.Pairwise (· < ·)) :
    vacuum (annihilators L (word T)) = if L=T then 1 else 0 := by
  induction L generalizing T with
  | nil =>
    simp only [annihilators_nil, Module.End.one_apply, vacuum_word]
    by_cases h : T=[] <;> simp [h, eq_comm]
  | cons j L ih =>
    cases T with
    | nil => simp [annihilators_cons]
    | cons k T =>
      obtain ⟨hjL, hL'⟩ := List.pairwise_cons.mp hL
      obtain ⟨hkT, hT'⟩ := List.pairwise_cons.mp hT
      by_cases he : j=k
      · subst k
        have hjT : j ∉ T := fun h => (lt_irrefl j) (hkT j h)
        rw [annihilators_cons]
        change vacuum (annihilators L (annihilate j (create j (word T)))) = _
        rw [annihilate_create, annihilate_word_absent j T hjT]
        simp only [↓reduceIte, one_smul, map_zero, sub_zero]
        rw [ih T hL' hT']
        simp
      · rcases lt_or_gt_of_ne he with hlt | hgt
        · have hjT : j ∉ k::T := by
            intro hm
            rcases List.mem_cons.mp hm with h | h
            · exact he h
            · exact (lt_irrefl j) (lt_trans hlt (hkT j h))
          rw [annihilators_cons]
          change vacuum (annihilators L (annihilate j (word (k::T)))) = _
          rw [annihilate_word_absent j (k::T) hjT]
          simp [he]
        · have hkL : k ∉ j::L := by
            intro hm
            rcases List.mem_cons.mp hm with h | h
            · exact he h.symm
            · exact (lt_irrefl k) (lt_trans hgt (hjL k h))
          rw [word_cons, annihilators_create_absent k (j::L) hkL]
          rw [map_smul, vacuum_create, smul_zero]
          simp [he]

def matrixUnit (I J : Finset HyperbolicSpinor.J) : Module.End ℝ S7 :=
  Algebra.lmul ℝ S7 (spinBasis I) * vacuum * annihilators (ordered J)

theorem matrixUnit_basis (I J T : Finset HyperbolicSpinor.J) :
    matrixUnit I J (spinBasis T) = if J=T then spinBasis I else 0 := by
  change spinBasis I * vacuum (annihilators (ordered J) (spinBasis T)) = _
  rw [basis_word T, annihilators_vacuum_pairing _ _ (ordered_pairwise J) (ordered_pairwise T)]
  have he : ordered J = ordered T ↔ J=T := by
    constructor
    · intro h
      ext i
      simp only [← mem_ordered, h]
    · exact congrArg ordered
  simp [he]

end HyperbolicSpinor
