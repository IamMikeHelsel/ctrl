import CaseTwo
import GreedyExtension
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Optimize the actual Case 2 expression after its graph construction.
This scalar lemma has no graph-existence premise. -/
theorem case_two_scalar_bound (a b t R e : ℚ)
    (hab : a ≤ b) (hthird : 2 * t ≤ 3 * a)
    (hR : R ≤ (2 * t - a - b) / 2)
    (he : e ≤ (t - a) * (b - a)) :
    e - (t - a) * (2 * t - a - b) / 2 + b * (t - b) / 2 +
      (t - b) ^ 2 / 4 + ((t - a) + (t - b) / 2) * R - 3 * R ^ 2 / 4 ≤
      a * (t - a) / 2 := by
  have h1 := mul_nonneg (sub_nonneg.mpr hthird) (sub_nonneg.mpr hab)
  have h2 := mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hab)
  nlinarith [sq_nonneg (b - a), sq_nonneg ((2 * t - a - b) / 2 - R)]

/-- Complete even-order graph construction from a maximum independent set
of density at least one third. The only envelope premise is an elementary
one-variable quadratic bound, not a graph theorem. Both completion branches
and the finite averaging/selection are proved. BCL is not needed locally. -/
theorem completion_from_maximum_independent
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (A : Finset V) (hA : A.Nonempty) (hAind : G.IsIndepSet (A : Set V))
    (hmax : ∀ C : Finset V, G.IsIndepSet (C : Set V) → C.card ≤ A.card)
    (t : ℕ) (hhalf : 2 * t = Fintype.card V)
    (hAt : A.card < t) (hthird : 2 * t ≤ 3 * A.card)
    (q : ℚ)
    (henvelope : ∀ b : ℚ, (A.card : ℚ) ≤ b → b ≤ (t : ℚ) →
      ((t : ℚ) - (A.card : ℚ)) * (b - (A.card : ℚ)) + b * ((t : ℚ) - b) / 2 ≤ q) :
    HasFractionalHalfBound G q := by
  classical
  let k : ℚ := (t : ℚ) - (A.card : ℚ)
  have hzero : (edgeCountOn G A : ℚ) = 0 := by
    rw [← edgeCost_finsetIndicator]
    exact edgeCost_eq_zero_of_support_subset_indep G hAind (by
      intro v hv
      by_contra hn
      have hn' : v ∉ A := hn
      exact hv (by simp [finsetIndicator, hn']))
  obtain ⟨B, hAB, hBt, hcost, hstop⟩ := exists_greedy_extension G A t k hAt.le
  rw [hzero, zero_add] at hcost
  have haB : A.card ≤ B.card := Finset.card_le_card hAB
  have haBQ : (A.card : ℚ) ≤ (B.card : ℚ) := by exact_mod_cast haB
  have hBtQ : (B.card : ℚ) ≤ (t : ℚ) := by exact_mod_cast hBt
  have hqB := henvelope (B.card : ℚ) haBQ hBtQ
  rcases hstop with heq | hstop
  · apply hasFractionalHalfBound_of_hasExactSparseHalf G
    refine ⟨B, by omega, ?_⟩
    rw [heq] at hcost hqB
    dsimp [k] at hcost
    nlinarith
  obtain ⟨D, hBD, hDcard, hdegrees⟩ := exists_low_degree_candidates G htri B A.card hmax
  let m : ℕ := t - B.card
  have hmadd : B.card + m = t := Nat.add_sub_of_le hBt
  have hmQ : (m : ℚ) = (t : ℚ) - (B.card : ℚ) := by
    dsimp [m]
    exact Nat.cast_sub hBt
  have hDfull : D.card = 2 * t - A.card - B.card := by omega
  have hDQ : (D.card : ℚ) = 2 * (t : ℚ) - (A.card : ℚ) - (B.card : ℚ) := by
    rw [hDfull, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hmD : m ≤ D.card := by omega
  have hBne : B.Nonempty := hA.mono hAB
  by_cases hcase : ∃ v ∈ B, m ≤ (D.filter fun z => G.Adj v z).card
  · obtain ⟨v, hv, hneigh⟩ := hcase
    obtain ⟨profile, hp, hc⟩ := fractional_half_of_neighborhood_completion
      G htri B D v m ((B.card : ℚ) / 2) hBD (by omega) hneigh hdegrees
    refine ⟨profile, hp, ?_⟩
    rw [hmQ] at hc
    dsimp [k] at hcost
    nlinarith
  · push_neg at hcase
    have hdegBoth : ∀ z ∈ D, k ≤ ((B.filter fun v => G.Adj z v).card : ℚ) ∧
        ((B.filter fun v => G.Adj z v).card : ℚ) ≤ (B.card : ℚ) / 2 := by
      intro z hz
      have hzB : z ∉ B := fun hzB => Finset.disjoint_left.mp hBD hzB hz
      exact ⟨(hstop z hzB).le, hdegrees z hz⟩
    obtain ⟨R, _hR0, hRcap, profile, hp, hc⟩ :=
      case_two_fractional_half G htri B D m k hBne hBD (by omega) hmD hcase hdegBoth
    rw [hmQ, hDQ] at hc
    rw [hDQ] at hRcap
    have hthirdQ : (2 : ℚ) * (t : ℚ) ≤ 3 * (A.card : ℚ) := by exact_mod_cast hthird
    have hbound := case_two_scalar_bound (A.card : ℚ) (B.card : ℚ) (t : ℚ) R
      (edgeCountOn G B : ℚ) haBQ hthirdQ hRcap hcost
    have hqA := henvelope (A.card : ℚ) le_rfl (by exact_mod_cast hAt.le)
    refine ⟨profile, hp, ?_⟩
    dsimp [k] at hc
    nlinarith

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.case_two_scalar_bound
#print axioms Erdos128.CompletionBridge.completion_from_maximum_independent
