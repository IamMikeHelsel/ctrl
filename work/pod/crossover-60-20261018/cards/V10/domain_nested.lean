import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
namespace CampaignV10
/-- Positive-depth cone feasibility is monotone in the externally fixed threshold. -/
theorem cone_threshold_monotone {E : Type*} [NormedAddCommGroup E]
    (residual : E) (depth gamma larger : ℝ) (hd : 0 ≤ depth)
    (hgl : gamma ≤ larger) (h : ‖residual‖ ≤ gamma*depth) :
    ‖residual‖ ≤ larger*depth :=
  h.trans (mul_le_mul_of_nonneg_right hgl hd)

/-- The same witness, gauge and positive depths survive a threshold increase.
    No existence of a minimum or closedness of the feasible set is asserted. -/
theorem multiview_feasibility_monotone {World View E : Type*}
    [NormedAddCommGroup E]
    (admissible : World → Prop) (residual : View → World → E)
    (depth : View → World → ℝ) (gamma larger : ℝ) (hgl : gamma ≤ larger)
    (h : ∃ w, admissible w ∧ ∀ i, 0 < depth i w ∧ ‖residual i w‖ ≤ gamma*depth i w) :
    ∃ w, admissible w ∧ ∀ i, 0 < depth i w ∧ ‖residual i w‖ ≤ larger*depth i w := by
  obtain ⟨w,hw,hi⟩ := h
  refine ⟨w,hw,fun i => ?_⟩
  exact ⟨(hi i).1, cone_threshold_monotone (residual i w) (depth i w) gamma larger
    (le_of_lt (hi i).1) hgl (hi i).2⟩
end CampaignV10
#print axioms CampaignV10.cone_threshold_monotone
#print axioms CampaignV10.multiview_feasibility_monotone
