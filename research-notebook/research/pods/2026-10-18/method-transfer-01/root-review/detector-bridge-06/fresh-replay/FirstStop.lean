module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LeanControls.FirstStop
open Set

/-- A first zero exists if continuous forward velocity is nonpositive by H.
The conclusion records positive velocity before the first zero; it says nothing
about the motion after that instant. -/
theorem exists_first_zero {H : ℝ} (hH : 0 ≤ H) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc 0 H)) (hv0 : 0 ≤ v 0) (hvH : v H ≤ 0) :
    ∃ T ∈ Icc 0 H, v T = 0 ∧ ∀ t ∈ Ico 0 T, 0 < v t := by
  have hex : ∃ t ∈ Icc 0 H, v t = 0 :=
    intermediate_value_Icc' hH hv ⟨hvH, hv0⟩
  let Z : Set ℝ := Icc 0 H ∩ v ⁻¹' {0}
  have hZclosed : IsClosed Z :=
    hv.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZcompact : IsCompact Z :=
    isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
  have hZne : Z.Nonempty := by
    obtain ⟨t, ht, hvt⟩ := hex
    exact ⟨t, ht, hvt⟩
  obtain ⟨T, hT, hmin⟩ := hZcompact.exists_isMinOn hZne continuousOn_id
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro t ht
  by_contra hpos
  have hvt : v t ≤ 0 := le_of_not_gt hpos
  have hvsmall : ContinuousOn v (Icc 0 t) :=
    hv.mono (Icc_subset_Icc le_rfl (le_trans ht.2.le hT.1.2))
  obtain ⟨s, hs, hvs⟩ := intermediate_value_Icc' ht.1 hvsmall ⟨hvt, hv0⟩
  have hsZ : s ∈ Z := ⟨⟨hs.1, le_trans hs.2 (le_trans ht.2.le hT.1.2)⟩, hvs⟩
  have hTs : T ≤ s := hmin hsZ
  linarith [hs.2, ht.2]

/-- A whole-horizon position envelope transfers to the first-stop prefix.
The physical flow/envelope proof must supply hpath independently. -/
theorem first_zero_with_travel_bound {H L : ℝ} (hH : 0 ≤ H)
    {x v : ℝ → ℝ} (hv : ContinuousOn v (Icc 0 H))
    (hv0 : 0 ≤ v 0) (hvH : v H ≤ 0)
    (hpath : ∀ t ∈ Icc 0 H, x t ≤ L) :
    ∃ T ∈ Icc 0 H, v T = 0 ∧ (∀ t ∈ Ico 0 T, 0 < v t) ∧
      ∀ t ∈ Icc 0 T, x t ≤ L := by
  obtain ⟨T,hT,hzero,hbefore⟩ := exists_first_zero hH hv hv0 hvH
  exact ⟨T,hT,hzero,hbefore,fun t ht => hpath t ⟨ht.1,ht.2.trans hT.2⟩⟩

end LeanControls.FirstStop
#print axioms LeanControls.FirstStop.exists_first_zero
#print axioms LeanControls.FirstStop.first_zero_with_travel_bound
