import Mathlib

/-!
# Zames (1966) incremental small-gain: well-posedness of the feedback loop

`ControlsLean/Controls/SmallGain.lean` proves the bound assuming a solution exists. Here:
if `G₁, G₂` are Lipschitz (incremental gains `γ₁, γ₂`) on complete signal spaces with
`γ₁ γ₂ < 1`, then for every input `(u₁, u₂)` the loop `e₁ = u₁ + G₂ e₂`, `e₂ = u₂ + G₁ e₁`
has a unique solution, it depends Lipschitz-continuously on the inputs, and Picard
iteration converges to it.
-/

open Filter Topology NNReal

namespace ClassicsFrequency

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The loop map on `e₁` obtained by eliminating `e₂`. -/
def loopMap (G₁ : E → F) (G₂ : F → E) (u₁ : E) (u₂ : F) (e₁ : E) : E :=
  u₁ + G₂ (u₂ + G₁ e₁)

theorem loopMap_lipschitz {G₁ : E → F} {G₂ : F → E} {γ₁ γ₂ : ℝ≥0}
    (h₁ : LipschitzWith γ₁ G₁) (h₂ : LipschitzWith γ₂ G₂) (u₁ : E) (u₂ : F) :
    LipschitzWith (γ₂ * γ₁) (loopMap G₁ G₂ u₁ u₂) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [loopMap, dist_add_left]
  calc dist (G₂ (u₂ + G₁ x)) (G₂ (u₂ + G₁ y)) ≤ γ₂ * dist (u₂ + G₁ x) (u₂ + G₁ y) :=
        h₂.dist_le_mul _ _
    _ = γ₂ * dist (G₁ x) (G₁ y) := by rw [dist_add_left]
    _ ≤ γ₂ * (γ₁ * dist x y) := by gcongr; exact h₁.dist_le_mul _ _
    _ = ↑(γ₂ * γ₁) * dist x y := by push_cast; ring

theorem loopMap_contracting [CompleteSpace E] {G₁ : E → F} {G₂ : F → E} {γ₁ γ₂ : ℝ≥0}
    (h₁ : LipschitzWith γ₁ G₁) (h₂ : LipschitzWith γ₂ G₂) (hγ : γ₁ * γ₂ < 1)
    (u₁ : E) (u₂ : F) : ContractingWith (γ₂ * γ₁) (loopMap G₁ G₂ u₁ u₂) :=
  ⟨by rwa [mul_comm], loopMap_lipschitz h₁ h₂ u₁ u₂⟩

/-- **Incremental small-gain theorem (well-posedness).** Existence and uniqueness of the
closed-loop signals. -/
theorem small_gain_wellPosed [CompleteSpace E] {G₁ : E → F} {G₂ : F → E} {γ₁ γ₂ : ℝ≥0}
    (h₁ : LipschitzWith γ₁ G₁) (h₂ : LipschitzWith γ₂ G₂) (hγ : γ₁ * γ₂ < 1)
    (u₁ : E) (u₂ : F) :
    ∃! e : E × F, e.1 = u₁ + G₂ e.2 ∧ e.2 = u₂ + G₁ e.1 := by
  have hc := loopMap_contracting h₁ h₂ hγ u₁ u₂
  set x := ContractingWith.fixedPoint _ hc
  have hx : loopMap G₁ G₂ u₁ u₂ x = x := ContractingWith.fixedPoint_isFixedPt hc
  refine ⟨(x, u₂ + G₁ x), ⟨hx.symm, rfl⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have hfix : Function.IsFixedPt (loopMap G₁ G₂ u₁ u₂) a := by
    simp only at ha hb
    show u₁ + G₂ (u₂ + G₁ a) = a
    rw [← hb, ← ha]
  have : a = x := hc.fixedPoint_unique hfix
  simp only at hb
  subst this
  exact Prod.ext rfl hb

/-- **Incremental closed-loop gain.** Two solutions driven by different inputs satisfy
`‖e₁ - e₁'‖ ≤ (‖u₁ - u₁'‖ + γ₂ ‖u₂ - u₂'‖) / (1 - γ₁ γ₂)`. -/
theorem small_gain_incremental {G₁ : E → F} {G₂ : F → E} {γ₁ γ₂ : ℝ≥0}
    (h₁ : LipschitzWith γ₁ G₁) (h₂ : LipschitzWith γ₂ G₂) (hγ : γ₁ * γ₂ < 1)
    {u₁ u₁' e₁ e₁' : E} {u₂ u₂' e₂ e₂' : F}
    (he₁ : e₁ = u₁ + G₂ e₂) (he₂ : e₂ = u₂ + G₁ e₁)
    (he₁' : e₁' = u₁' + G₂ e₂') (he₂' : e₂' = u₂' + G₁ e₁') :
    ‖e₁ - e₁'‖ ≤ (‖u₁ - u₁'‖ + γ₂ * ‖u₂ - u₂'‖) / (1 - γ₁ * γ₂) := by
  have hγ' : (γ₁ : ℝ) * γ₂ < 1 := by exact_mod_cast hγ
  have l₁ : ‖G₁ e₁ - G₁ e₁'‖ ≤ γ₁ * ‖e₁ - e₁'‖ := h₁.norm_sub_le _ _
  have l₂ : ‖G₂ e₂ - G₂ e₂'‖ ≤ γ₂ * ‖e₂ - e₂'‖ := h₂.norm_sub_le _ _
  have b₁ : ‖e₁ - e₁'‖ ≤ ‖u₁ - u₁'‖ + ‖G₂ e₂ - G₂ e₂'‖ := by
    rw [he₁, he₁', add_sub_add_comm]; exact norm_add_le _ _
  have b₂ : ‖e₂ - e₂'‖ ≤ ‖u₂ - u₂'‖ + ‖G₁ e₁ - G₁ e₁'‖ := by
    rw [he₂, he₂', add_sub_add_comm]; exact norm_add_le _ _
  have g2 : (0 : ℝ) ≤ γ₂ := γ₂.2
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left b₂ g2, mul_le_mul_of_nonneg_left l₁ g2]

/-- Picard iteration of the loop converges to the closed-loop solution. -/
theorem small_gain_picard_tendsto [CompleteSpace E] {G₁ : E → F} {G₂ : F → E} {γ₁ γ₂ : ℝ≥0}
    (h₁ : LipschitzWith γ₁ G₁) (h₂ : LipschitzWith γ₂ G₂) (hγ : γ₁ * γ₂ < 1)
    (u₁ : E) (u₂ : F) (x₀ : E) :
    Tendsto (fun n => (loopMap G₁ G₂ u₁ u₂)^[n] x₀) atTop
      (𝓝 (ContractingWith.fixedPoint _ (loopMap_contracting h₁ h₂ hγ u₁ u₂))) :=
  ContractingWith.tendsto_iterate_fixedPoint _ x₀

/-! ### Linear (operator-norm) version: `ℓ₂`-type small gain -/

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- For bounded linear `G₁, G₂` with `‖G₁‖ ‖G₂‖ < 1`, the loop is well posed and
`‖e₁‖ ≤ (‖u₁‖ + ‖G₂‖ ‖u₂‖) / (1 - ‖G₁‖ ‖G₂‖)`. -/
theorem small_gain_linear_opNorm [CompleteSpace E] (G₁ : E →L[ℝ] F) (G₂ : F →L[ℝ] E)
    (hγ : ‖G₁‖ * ‖G₂‖ < 1) (u₁ : E) (u₂ : F) :
    ∃! e : E × F, (e.1 = u₁ + G₂ e.2 ∧ e.2 = u₂ + G₁ e.1) ∧
      ‖e.1‖ ≤ (‖u₁‖ + ‖G₂‖ * ‖u₂‖) / (1 - ‖G₁‖ * ‖G₂‖) := by
  have hγ' : ‖G₁‖₊ * ‖G₂‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe]; simpa using hγ
  obtain ⟨e, he, huniq⟩ :=
    small_gain_wellPosed G₁.lipschitz G₂.lipschitz hγ' u₁ u₂
  refine ⟨e, ⟨he, ?_⟩, fun e' h' => huniq e' h'.1⟩
  have := small_gain_incremental G₁.lipschitz G₂.lipschitz hγ' he.1 he.2
    (u₁' := 0) (u₂' := 0) (e₁' := 0) (e₂' := 0) (by simp) (by simp)
  simpa using this

end ClassicsFrequency
