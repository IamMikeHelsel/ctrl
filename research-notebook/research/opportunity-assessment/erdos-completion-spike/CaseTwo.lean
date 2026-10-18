import FiniteAveraging
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The actual averaged Case 2 construction, before optimizing its scalar
parameter R. Every witness in the conclusion is a genuine fractional half. -/
theorem case_two_fractional_half
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (B D : Finset V) (m : ℕ) (k : ℚ)
    (hB : B.Nonempty) (hdis : Disjoint B D)
    (hhalf : 2 * (B.card + m) = Fintype.card V)
    (hmD : m ≤ D.card)
    (hcase : ∀ v ∈ B, (D.filter fun z => G.Adj v z).card < m)
    (hdegrees : ∀ z ∈ D, k ≤ ((B.filter fun v => G.Adj z v).card : ℚ) ∧
      ((B.filter fun v => G.Adj z v).card : ℚ) ≤ (B.card : ℚ) / 2) :
    ∃ R : ℚ, 0 ≤ R ∧ R ≤ (D.card : ℚ) / 2 ∧
      HasFractionalHalfBound G
        ((edgeCountOn G B : ℚ) - k * (D.card : ℚ) / 2 +
          (B.card : ℚ) * (m : ℚ) / 2 + (m : ℚ) ^ 2 / 4 +
          (k + (m : ℚ) / 2) * R - 3 * R ^ 2 / 4) := by
  classical
  let b : ℚ := B.card
  let d : ℚ := D.card
  let E (v : V) : Finset V := D.filter fun z => G.Adj v z
  let r (v : V) : ℚ := (E v).card
  let deg (z : V) : ℚ := (B.filter fun v => G.Adj z v).card
  let w (v : V) : ℚ := ((m : ℚ) - r v) / (d - r v)
  let profile (v : V) : V → ℚ := completionProfile B D (E v) (w v)
  let cost (v : V) : ℚ := edgeCost G (profile v)
  let cross (v : V) : ℚ := 2 * edgeBilin G (finsetIndicator (E v)) (finsetIndicator B)
  let R : ℚ := (∑ z ∈ D, deg z) / b
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast hB.card_pos
  have htotal : (∑ v ∈ B, r v) = ∑ z ∈ D, deg z := neighborhood_size_sum G B D
  have hmeanD : (∑ z ∈ D, deg z) = b * R := by
    dsimp [R]
    rw [mul_div_cancel₀ _ (ne_of_gt hb)]
  have hmean : (∑ v ∈ B, r v) = (B.card : ℚ) * R := htotal.trans hmeanD
  have hR0 : 0 ≤ R := div_nonneg (Finset.sum_nonneg (fun z _ => Nat.cast_nonneg _)) hb.le
  have hRcap : R ≤ d / 2 := by
    have hd : (∑ z ∈ D, deg z) ≤ d * (b / 2) := by
      calc
        _ ≤ ∑ _z ∈ D, b / 2 := Finset.sum_le_sum (fun z hz => (hdegrees z hz).2)
        _ = _ := by simp [d]
    dsimp [R]
    apply (div_le_iff₀ hb).mpr
    nlinarith
  have hcross : (∑ v ∈ B, cross v) ≤
      b * ((k + b / 2) * R - k * d / 2) := by
    have hid : (∑ v ∈ B, cross v) = ∑ z ∈ D, (deg z) ^ 2 :=
      neighborhood_cross_cost_sum G B D
    rw [hid]
    calc
      _ ≤ ∑ z ∈ D, ((k + b / 2) * deg z - k * b / 2) := Finset.sum_le_sum (by
        intro z hz
        obtain ⟨hl, hu⟩ := hdegrees z hz
        have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (sub_nonpos.mpr hu)
        dsimp [deg, b] at *
        nlinarith)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        rw [hmeanD]
        dsimp [d]
        ring
  have hfeasible : ∀ v ∈ B, IsFractionalHalf (profile v) := by
    intro v hv
    have hED : E v ⊆ D := Finset.filter_subset _ _
    have hrv : (E v).card < m := hcase v hv
    have hp := weighted_profile_is_fractional_half B D (E v) (B.card + m)
      hdis hED (by omega) (by omega) (by omega) hhalf
    convert hp using 1 <;> dsimp [profile, w, r, d] <;> congr 1 <;> push_cast <;> ring
  have hcost : ∀ v ∈ B, cost v ≤
      ((edgeCountOn G B : ℚ) + b * (m : ℚ) / 2 + (m : ℚ) ^ 2 / 4) +
      cross v + (-b / 2 + (m : ℚ) / 2) * r v - (3 / 4 : ℚ) * (r v) ^ 2 := by
    intro v hv
    have hED : E v ⊆ D := Finset.filter_subset _ _
    have hrv : r v < (m : ℚ) := by
      dsimp [r, E]
      exact_mod_cast hcase v hv
    have hmQ : (m : ℚ) ≤ d := by
      dsimp [d]
      exact_mod_cast hmD
    have hden : 0 < d - r v := by linarith
    have hw : 0 ≤ w v := div_nonneg (by linarith) hden.le
    have hF : ((D \ E v).card : ℚ) = d - r v := by
      rw [Finset.card_sdiff_of_subset hED, Nat.cast_sub (Finset.card_le_card hED)]
    have hfill : w v * ((D \ E v).card : ℚ) = (m : ℚ) - r v := by
      rw [hF]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hind : G.IsIndepSet (E v : Set V) :=
      (G.isIndepSet_neighborSet_of_triangleFree htri v).mono (by
        intro z hz
        exact (Finset.mem_filter.mp hz).2)
    have hc := weighted_profile_cost_bound G htri B D (E v) (w v) hw hED hind
      (fun z hz => (hdegrees z hz).2)
    have heq : (∑ z ∈ E v, ((B.filter fun u => G.Adj z u).card : ℚ)) = cross v :=
      (cross_indicator_eq_degree_sum G B (E v)).symm
    rw [heq] at hc
    have halgebra :
        (edgeCountOn G B : ℚ) + cross v +
          w v * ((D \ E v).card : ℚ) * (B.card : ℚ) / 2 +
          w v * ((D \ E v).card : ℚ) * ((E v).card : ℚ) +
          w v ^ 2 * ((D \ E v).card : ℚ) ^ 2 / 4 =
        ((edgeCountOn G B : ℚ) + b * (m : ℚ) / 2 + (m : ℚ) ^ 2 / 4) +
          cross v + (-b / 2 + (m : ℚ) / 2) * r v - (3 / 4 : ℚ) * (r v) ^ 2 := by
      rw [← mul_pow, hfill]
      dsimp [b, r]
      ring
    exact hc.trans_eq halgebra
  obtain ⟨v, hv, hcostv⟩ := exists_le_concave_average B hB cost cross r
    ((edgeCountOn G B : ℚ) + b * (m : ℚ) / 2 + (m : ℚ) ^ 2 / 4)
    (-b / 2 + (m : ℚ) / 2) (3 / 4) ((k + b / 2) * R - k * d / 2) R
    (by norm_num) hcost hcross hmean
  refine ⟨R, hR0, hRcap, profile v, hfeasible v hv, ?_⟩
  convert hcostv using 1 <;> dsimp [cost, b, d] <;> ring

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.case_two_fractional_half
