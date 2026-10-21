import domain_coverage

namespace CampaignS04
/-- The last-mile theorem has the original leakage parameter, not producer branch labels.
    `rows` represents all unchanged prior/observation constraints; `safe` is the
    common property actually proved on each complete sign polyhedron. -/
theorem original_model_acceptance (lo hi : ℝ)
    (rows safe : ℝ → ℝ → ℝ → Prop)
    (positive : ∀ w d q, rows w d q → 0 ≤ d → lo * d ≤ q → q ≤ hi * d → safe w d q)
    (negative : ∀ w d q, rows w d q → d ≤ 0 → hi * d ≤ q → q ≤ lo * d → safe w d q) :
    ∀ w d lam, lo ≤ lam → lam ≤ hi → rows w d (lam * d) → safe w d (lam * d) := by
  intro w d lam hlo hhi hrows
  have cover := leakage_branch_cover d (lam * d) lo hi ⟨lam, hlo, hhi, rfl⟩
  rcases cover with h | h
  · exact positive w d (lam * d) hrows h.1 h.2.1 h.2.2
  · exact negative w d (lam * d) hrows h.1 h.2.1 h.2.2

/-- Dropping interval nonemptiness creates a spurious zero-d branch. -/
theorem empty_interval_counterexample :
    ((0 : ℝ) ≤ 0 ∧ 1 * 0 ≤ 0 ∧ 0 ≤ 0 * 0) ∧
    ¬ (∃ lam : ℝ, 1 ≤ lam ∧ lam ≤ 0 ∧ 0 = lam * 0) := by
  constructor
  · norm_num
  · rintro ⟨lam, hlo, hhi, _⟩
    linarith

/-- The frozen source's interval has an explicit valid endpoint witness. -/
theorem frozen_leakage_interval_nonempty :
    ∃ lam : ℝ, (1 / 5 : ℝ) ≤ lam ∧ lam ≤ (3 / 10 : ℝ) := by
  exact ⟨1 / 5, le_rfl, by norm_num⟩
end CampaignS04
#print axioms CampaignS04.original_model_acceptance
#print axioms CampaignS04.empty_interval_counterexample
#print axioms CampaignS04.frozen_leakage_interval_nonempty
