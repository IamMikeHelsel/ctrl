import MatrixUnits

noncomputable section
namespace HyperbolicSpinor
open GUClifford

/-- Every factor uses annihilation after creation. -/
def vacuumElement : Cl :=
  ((List.ofFn (fun i : J => i)).map (fun i => annihilatorElement i * creatorElement i)).prod

theorem vacuum_image : splitAction vacuumElement = vacuum := by
  simp [vacuumElement, vacuum, factors,
    map_mul, annihilator_image, creator_image, emptyFactor]

def creatorWordElement (L : List J) : Cl := (L.map creatorElement).prod

theorem creatorWord_image (L : List J) :
    splitAction (creatorWordElement L) = Algebra.lmul ℝ S7 (word L) := by
  induction L with
  | nil =>
    apply LinearMap.ext
    intro x
    simp [creatorWordElement, word]
  | cons j L ih =>
    change splitAction (creatorElement j * creatorWordElement L) = _
    rw [map_mul, creator_image, ih, word_cons]
    apply LinearMap.ext
    intro x
    simp [create, mul_assoc]

def annihilatorWordElement (L : List J) : Cl := (L.reverse.map annihilatorElement).prod

theorem annihilatorWord_image (L : List J) :
    splitAction (annihilatorWordElement L) = annihilators L := by
  simp [annihilatorWordElement, annihilators, map_list_prod, List.map_map,
    annihilator_image, Function.comp_def]

def matrixUnitElement (I J : Finset HyperbolicSpinor.J) : Cl :=
  creatorWordElement (ordered I) * vacuumElement * annihilatorWordElement (ordered J)

theorem matrixUnit_image (I J : Finset HyperbolicSpinor.J) :
    splitAction (matrixUnitElement I J) = matrixUnit I J := by
  simp only [matrixUnitElement, map_mul, creatorWord_image, vacuum_image, annihilatorWord_image]
  rw [← basis_word]
  rfl

/-- An explicit preimage is the finite sum of the actual Clifford matrix units. -/
def preimage (f : Module.End ℝ S7) : Cl :=
  ∑ J : Finset HyperbolicSpinor.J, ∑ I : Finset HyperbolicSpinor.J,
    (spinBasis.repr (f (spinBasis J)) I) • matrixUnitElement I J

theorem preimage_image (f : Module.End ℝ S7) : splitAction (preimage f) = f := by
  apply spinBasis.ext
  intro T
  simp only [preimage, map_sum, map_smul, matrixUnit_image,
    LinearMap.sum_apply, LinearMap.smul_apply, matrixUnit_basis]
  simp only [smul_ite, smul_zero, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact spinBasis.sum_repr (f (spinBasis T))

theorem splitAction_surjective : Function.Surjective splitAction :=
  fun f => ⟨preimage f, preimage_image f⟩

theorem splitMatrix_surjective : Function.Surjective splitMatrix := by
  intro A
  obtain ⟨f, hf⟩ := (LinearMap.toMatrixAlgEquiv spinBasis).surjective A
  obtain ⟨x, hx⟩ := splitAction_surjective f
  exact ⟨x, by simpa [splitMatrix, hx] using hf⟩

end HyperbolicSpinor
