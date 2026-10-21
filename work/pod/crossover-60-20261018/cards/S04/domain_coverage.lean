import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace CampaignS04

/-- Semantic coverage is a premise about actual worlds, not merely branch labels. -/
theorem semantic_cover {World Branch : Type*}
    (admissible safe : World → Prop) (inBranch : Branch → World → Prop)
    (required : Set Branch)
    (cover : ∀ w, admissible w → ∃ b ∈ required, inBranch b w)
    (checked : ∀ b ∈ required, ∀ w, admissible w → inBranch b w → safe w) :
    ∀ w, admissible w → safe w := by
  intro w hw
  obtain ⟨b, hb, hbw⟩ := cover w hw
  exact checked b hb w hw hbw

/-- A checked surrogate branch must contain its corresponding real branch. -/
theorem model_bridge_cover {World Branch : Type*}
    (admissible safe : World → Prop) (realBranch checkedBranch : Branch → World → Prop)
    (cover : ∀ w, admissible w → ∃ b, realBranch b w)
    (bridge : ∀ b w, admissible w → realBranch b w → checkedBranch b w)
    (checked : ∀ b w, admissible w → checkedBranch b w → safe w) :
    ∀ w, admissible w → safe w := by
  intro w hw
  obtain ⟨b, hb⟩ := cover w hw
  exact checked b w hw (bridge b w hw hb)

/-- Complete labels alone permit two copies of the same safe half-domain. -/
theorem label_coverage_is_not_semantic_coverage :
    (∀ _b : Bool, ∀ w : Bool, w = false → w = false) ∧
    ¬ (∀ w : Bool, w = false) := by
  constructor
  · intro b w hw
    exact hw
  · intro h
    have hf := h true
    cases hf

/-- Byte identity implies model identity only with an explicit faithful decoder bridge. -/
theorem binding_composition {Artifact Model : Type*}
    (decode : Artifact → Model) (required checked : Artifact)
    (property : Model → Prop) (bound : checked = required)
    (kernelChecked : property (decode checked)) : property (decode required) := by
  simpa only [bound] using kernelChecked

/-- Equal bytes cannot establish freshness: two epochs can share an artifact. -/
theorem content_identity_does_not_imply_epoch_identity :
    ∃ (artifactAt : Nat → Bool) (old current : Nat),
      artifactAt old = artifactAt current ∧ old ≠ current := by
  exact ⟨fun _ => false, 0, 1, rfl, by decide⟩

end CampaignS04
#print axioms CampaignS04.semantic_cover
#print axioms CampaignS04.model_bridge_cover
#print axioms CampaignS04.label_coverage_is_not_semantic_coverage
#print axioms CampaignS04.binding_composition
#print axioms CampaignS04.content_identity_does_not_imply_epoch_identity

namespace CampaignS04
/-- Exact semantic cover of the source checker's two sign polyhedra. -/
theorem leakage_branch_cover (d q lo hi : ℝ)
    (h : ∃ lam, lo ≤ lam ∧ lam ≤ hi ∧ q = lam * d) :
    (0 ≤ d ∧ lo * d ≤ q ∧ q ≤ hi * d) ∨
    (d ≤ 0 ∧ hi * d ≤ q ∧ q ≤ lo * d) := by
  obtain ⟨lam, hl, hu, rfl⟩ := h
  rcases le_total 0 d with hd | hd
  · left
    exact ⟨hd, mul_le_mul_of_nonneg_right hl hd, mul_le_mul_of_nonneg_right hu hd⟩
  · right
    exact ⟨hd, mul_le_mul_of_nonpos_right hu hd, mul_le_mul_of_nonpos_right hl hd⟩

/-- The branch union contains no spurious leakage worlds when lo ≤ hi. -/
theorem leakage_branch_sound (d q lo hi : ℝ) (hlh : lo ≤ hi)
    (h : (0 ≤ d ∧ lo * d ≤ q ∧ q ≤ hi * d) ∨
      (d ≤ 0 ∧ hi * d ≤ q ∧ q ≤ lo * d)) :
    ∃ lam, lo ≤ lam ∧ lam ≤ hi ∧ q = lam * d := by
  by_cases hd : d = 0
  · subst d
    have hq : q = 0 := by rcases h with h | h <;> simp_all <;> linarith
    exact ⟨lo, le_rfl, hlh, by simp [hq]⟩
  · refine ⟨q / d, ?_, ?_, by field_simp⟩
    · rcases h with h | h
      · exact (le_div_iff₀ (lt_of_le_of_ne h.1 (Ne.symm hd))).2 h.2.1
      · exact (le_div_iff_of_neg (lt_of_le_of_ne h.1 hd)).2 h.2.2
    · rcases h with h | h
      · exact (div_le_iff₀ (lt_of_le_of_ne h.1 (Ne.symm hd))).2 h.2.2
      · exact (div_le_iff_of_neg (lt_of_le_of_ne h.1 hd)).2 h.2.1
end CampaignS04
#print axioms CampaignS04.leakage_branch_cover
#print axioms CampaignS04.leakage_branch_sound
