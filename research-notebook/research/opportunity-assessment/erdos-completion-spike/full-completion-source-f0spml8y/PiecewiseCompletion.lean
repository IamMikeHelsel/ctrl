import CompletionEnvelope
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace Erdos128.CompletionBridge
open scoped BigOperators
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Unnormalized completion envelope when n=2t. The branch threshold
4a=3t is exactly alpha=3/8 in the paper. -/
def completionEnvelope (a t : ℚ) : ℚ :=
  if 4 * a ≤ 3 * t then 3 * a ^ 2 / 2 - 5 * a * t / 2 + 9 * t ^ 2 / 8
  else a * (t - a) / 2

theorem quadratic_le_completionEnvelope (a t b : ℚ) (hab : a ≤ b) :
    (t - a) * (b - a) + b * (t - b) / 2 ≤ completionEnvelope a t := by
  unfold completionEnvelope
  split_ifs with h
  · nlinarith [sq_nonneg (b - (3 * t / 2 - a))]
  · have hp := mul_nonneg (show 0 ≤ 4 * a - 3 * t by linarith) (sub_nonneg.mpr hab)
    nlinarith [sq_nonneg (b - a)]

theorem completionEnvelope_nonneg (a t : ℚ) (ha : 0 ≤ a) (hat : a ≤ t) :
    0 ≤ completionEnvelope a t := by
  have hp := mul_nonneg ha (sub_nonneg.mpr hat)
  unfold completionEnvelope
  split_ifs
  · nlinarith [sq_nonneg (a - 3 * t / 4)]
  · linarith

/-- The envelope decreases from independent-set density one third onward. -/
theorem completionEnvelope_antitone (x a t : ℚ) (ht : 0 ≤ t)
    (hthird : 2 * t ≤ 3 * x) (hxa : x ≤ a) :
    completionEnvelope a t ≤ completionEnvelope x t := by
  by_cases ha : 4 * a ≤ 3 * t
  · have hx : 4 * x ≤ 3 * t := by linarith
    simp only [completionEnvelope, if_pos ha, if_pos hx]
    have hp := mul_nonneg (sub_nonneg.mpr hxa) (show 0 ≤ 5 * t - 3 * (a + x) by linarith)
    nlinarith
  · by_cases hx : 4 * x ≤ 3 * t
    · simp only [completionEnvelope, if_neg ha, if_pos hx]
      have hp := mul_nonneg (show 0 ≤ 3 * t / 4 - x by linarith)
        (show 0 ≤ 5 * t - 3 * (3 * t / 4 + x) by linarith)
      have hq := mul_nonneg (show 0 ≤ a - 3 * t / 4 by linarith)
        (show 0 ≤ a + 3 * t / 4 - t by linarith)
      nlinarith
    · simp only [completionEnvelope, if_neg ha, if_neg hx]
      have hp := mul_nonneg (sub_nonneg.mpr hxa) (show 0 ≤ a + x - t by linarith)
      nlinarith

/-- The local completion theorem with the scalar envelope fully discharged. -/
theorem maximum_independent_completion
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (A : Finset V) (hA : A.Nonempty) (hAind : G.IsIndepSet (A : Set V))
    (hmax : ∀ C : Finset V, G.IsIndepSet (C : Set V) → C.card ≤ A.card)
    (t : ℕ) (hhalf : 2 * t = Fintype.card V)
    (hAt : A.card < t) (hthird : 2 * t ≤ 3 * A.card) :
    HasFractionalHalfBound G (completionEnvelope (A.card : ℚ) (t : ℚ)) :=
  completion_from_maximum_independent G htri A hA hAind hmax t hhalf hAt hthird
    _ (fun b hb _ => quadratic_le_completionEnvelope _ _ b hb)

/-- Complete even-order independent-set completion theorem. X need not be
maximum: a maximum independent set is selected internally. All graph,
profile, averaging and piecewise-optimization steps have proofs. -/
theorem independent_set_completion_even
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (X : Finset V) (hX : G.IsIndepSet (X : Set V))
    (t : ℕ) (hhalf : 2 * t = Fintype.card V)
    (hthird : 2 * t ≤ 3 * X.card) (hXt : X.card ≤ t) :
    HasFractionalHalfBound G (completionEnvelope (X.card : ℚ) (t : ℚ)) := by
  classical
  let F : Finset (Finset V) := Finset.univ.filter fun A => G.IsIndepSet (A : Set V)
  have hXF : X ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩
  obtain ⟨A, hAF, hmaxF⟩ := F.exists_max_image Finset.card ⟨X, hXF⟩
  have hAind : G.IsIndepSet (A : Set V) := (Finset.mem_filter.mp hAF).2
  have hmax : ∀ C : Finset V, G.IsIndepSet (C : Set V) → C.card ≤ A.card := by
    intro C hC
    exact hmaxF C (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩)
  have hXA : X.card ≤ A.card := hmax X hX
  by_cases hAt : t ≤ A.card
  · obtain ⟨S, hSA, hScard⟩ := Finset.exists_subset_card_eq hAt
    have hSind : G.IsIndepSet (S : Set V) := hAind.mono (by exact hSA)
    have hzero : edgeCost G (finsetIndicator S) = 0 :=
      edgeCost_eq_zero_of_support_subset_indep G hSind (by
        intro v hv
        by_contra hn
        have hn' : v ∉ S := hn
        exact hv (by simp [finsetIndicator, hn']))
    refine ⟨finsetIndicator S, isFractionalHalf_finsetIndicator (by omega), ?_⟩
    rw [hzero]
    exact completionEnvelope_nonneg _ _ (by positivity) (by exact_mod_cast hXt)
  · have hAt' : A.card < t := by omega
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨profile, hp, hc⟩ := maximum_independent_completion G htri A hA hAind hmax
      t hhalf hAt' (by omega)
    refine ⟨profile, hp, hc.trans ?_⟩
    exact completionEnvelope_antitone _ _ _ (by positivity)
      (by exact_mod_cast hthird) (by exact_mod_cast hXA)

/-- The exact deletion/completion/restoration result needed by the newer
argument, for even-order graphs and a cut side between n/3 and n/2.
No external completion or max-cut result is a hypothesis. -/
theorem deletion_completion_even
    (G : SimpleGraph V) [DecidableRel G.Adj] (htri : G.CliqueFree 3)
    (X : Finset V) (t : ℕ) (hhalf : 2 * t = Fintype.card V)
    (hthird : 2 * t ≤ 3 * X.card) (hXt : X.card ≤ t) :
    HasFractionalHalfBound G
      (completionEnvelope (X.card : ℚ) (t : ℚ) + (edgeCountOn G X : ℚ)) := by
  apply DeletionBridge.restore_fractional_half G X
  exact independent_set_completion_even (DeletionBridge.deleteInside G X)
    (DeletionBridge.deleteInside_cliqueFree G X htri) X
    (DeletionBridge.deleteInside_independent G X) t hhalf hthird hXt

end
end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.quadratic_le_completionEnvelope
#print axioms Erdos128.CompletionBridge.completionEnvelope_nonneg
#print axioms Erdos128.CompletionBridge.completionEnvelope_antitone
#print axioms Erdos128.CompletionBridge.maximum_independent_completion
#print axioms Erdos128.CompletionBridge.independent_set_completion_even
#print axioms Erdos128.CompletionBridge.deletion_completion_even
