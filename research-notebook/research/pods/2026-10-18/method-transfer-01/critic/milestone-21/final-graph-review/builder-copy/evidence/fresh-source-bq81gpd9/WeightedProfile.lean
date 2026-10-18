import CompletionBranch
set_option maxHeartbeats 1000000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Case 2's actual rational vertex profile, with E selected inside D. -/
def completionProfile (B D E : Finset V) (w : ℚ) (v : V) : ℚ :=
  finsetIndicator B v + finsetIndicator E v + w * finsetIndicator (D \ E) v

/-- The rational weight used by Case 2 gives a fractional half. The strict
cardinality gap rules out a zero denominator; the two target inequalities
are exactly the lower and upper feasibility requirements for the weight. -/
theorem weighted_profile_is_fractional_half
    (B D E : Finset V) (t : ℕ)
    (hdis : Disjoint B D) (hED : E ⊆ D)
    (hEt : B.card + E.card ≤ t) (htD : t ≤ B.card + D.card)
    (hgap : E.card < D.card) (hhalf : 2 * t = Fintype.card V) :
    IsFractionalHalf (completionProfile B D E
      (((t : ℚ) - (B.card : ℚ) - (E.card : ℚ)) /
        ((D.card : ℚ) - (E.card : ℚ)))) := by
  let w : ℚ := ((t : ℚ) - (B.card : ℚ) - (E.card : ℚ)) /
        ((D.card : ℚ) - (E.card : ℚ))
  change IsFractionalHalf (completionProfile B D E w)
  have hden : 0 < (D.card : ℚ) - (E.card : ℚ) := by
    have hgapQ : (E.card : ℚ) < (D.card : ℚ) := by exact_mod_cast hgap
    linarith
  have hEtQ : (B.card : ℚ) + (E.card : ℚ) ≤ (t : ℚ) := by exact_mod_cast hEt
  have htDQ : (t : ℚ) ≤ (B.card : ℚ) + (D.card : ℚ) := by exact_mod_cast htD
  have hw0 : 0 ≤ w := div_nonneg (by linarith) hden.le
  have hw1 : w ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hwprod : w * ((D.card : ℚ) - (E.card : ℚ)) =
      (t : ℚ) - (B.card : ℚ) - (E.card : ℚ) := div_mul_cancel₀ _ (ne_of_gt hden)
  constructor
  · intro v
    have hBD : ¬ (v ∈ B ∧ v ∈ D) := fun h => Finset.disjoint_left.mp hdis h.1 h.2
    have hEDv : v ∈ E → v ∈ D := fun h => hED h
    by_cases hb : v ∈ B <;> by_cases he : v ∈ E <;> by_cases hd : v ∈ D <;>
      simp_all [completionProfile, finsetIndicator]
  · simp only [completionProfile, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_finsetIndicator]
    have hcard : ((D \ E).card : ℚ) = (D.card : ℚ) - (E.card : ℚ) := by
      rw [Finset.card_sdiff_of_subset hED, Nat.cast_sub (Finset.card_le_card hED)]
    rw [hcard, hwprod]
    have hn : (2 : ℚ) * (t : ℚ) = (Fintype.card V : ℚ) := by exact_mod_cast hhalf
    linarith

/-- Exact six-part edge accounting of the constructed Case 2 profile.
The E-internal term vanishes by independence; all other contributions are
actual graph costs/incidences, not an assumed objective bound. -/
theorem weighted_profile_cost
    (G : SimpleGraph V) [DecidableRel G.Adj] (B D E : Finset V) (w : ℚ)
    (hind : G.IsIndepSet (E : Set V)) :
    edgeCost G (completionProfile B D E w) =
      (edgeCountOn G B : ℚ) +
      (∑ z ∈ E, ((B.filter fun v => G.Adj z v).card : ℚ)) +
      w * (∑ z ∈ D \ E, ((B.filter fun v => G.Adj z v).card : ℚ)) +
      w * (∑ z ∈ D \ E, ((E.filter fun v => G.Adj z v).card : ℚ)) +
      w ^ 2 * (edgeCountOn G (D \ E) : ℚ) := by
  have hz : edgeCost G (finsetIndicator E) = 0 :=
    edgeCost_eq_zero_of_support_subset_indep G hind (by
      intro v hv
      by_contra hn
      have hn' : v ∉ E := hn
      exact hv (by simp [finsetIndicator, hn']))
  change edgeCost G (fun v => (finsetIndicator B v + finsetIndicator E v) +
      w * finsetIndicator (D \ E) v) = _
  rw [edgeCost_add, edgeCost_add, edgeCost_smul, edgeBilin_add_left,
    edgeBilin_smul_right, edgeBilin_smul_right, hz,
    edgeCost_finsetIndicator, edgeCost_finsetIndicator]
  have hBE := cross_indicator_eq_degree_sum G B E
  have hBF := cross_indicator_eq_degree_sum G B (D \ E)
  have hEF := cross_indicator_eq_degree_sum G E (D \ E)
  rw [edgeBilin_comm G (finsetIndicator E) (finsetIndicator B)] at hBE
  rw [edgeBilin_comm G (finsetIndicator (D \ E)) (finsetIndicator B)] at hBF
  rw [edgeBilin_comm G (finsetIndicator (D \ E)) (finsetIndicator E)] at hEF
  rw [← hBE, ← hBF, ← hEF]
  ring

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.weighted_profile_is_fractional_half
#print axioms Erdos128.CompletionBridge.weighted_profile_cost
