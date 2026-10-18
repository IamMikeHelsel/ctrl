import Erdos128.ExternalInputs
import Erdos128.GraphRational

set_option linter.style.header false

/-!
# Balanced independent blow-ups

This file gives the exact finite identities behind the balanced-blow-up
argument.  The `k` clones of a vertex are indexed by `Fin k`; adjacency only
depends on the two original vertices.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The balanced independent `k`-fold blow-up of a graph. -/
def balancedBlowup (G : SimpleGraph V) (k : ℕ) : SimpleGraph (V × Fin k) :=
  G.comap Prod.fst

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem balancedBlowup_adj (G : SimpleGraph V) (k : ℕ)
    (u v : V × Fin k) :
    (balancedBlowup G k).Adj u v ↔ G.Adj u.1 v.1 :=
  Iff.rfl

instance balancedBlowup.instDecidableAdj
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (balancedBlowup G k).Adj := by
  unfold balancedBlowup
  infer_instance

/-- A symmetric weight on an unordered edge. -/
private def symEdgeWeight (x : V → ℚ) : Sym2 V → ℚ :=
  Sym2.lift ⟨fun u v ↦ x u * x v, by
    intro u v
    ring⟩

omit [DecidableEq V] in
private lemma edgeCost_eq_sum_symEdgeWeight
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    edgeCost G x = ∑ e ∈ G.edgeFinset, symEdgeWeight x e := by
  unfold edgeCost edgeBilin
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      change (x u * x v + x v * x u) / 2 = x u * x v
      ring

omit [DecidableEq V] in
/-- The quadratic edge cost is half of the corresponding ordered sum. -/
private lemma two_mul_edgeCost_eq_ordered_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) :
    2 * edgeCost G x =
      ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
  classical
  rw [edgeCost_eq_sum_symEdgeWeight]
  rw [Finset.mul_sum]
  have hfiber :
      ∑ e ∈ G.edgeFinset,
          ∑ d ∈ (Finset.univ.filter fun d : G.Dart ↦ d.edge = e),
            x d.fst * x d.snd =
        ∑ d : G.Dart, x d.fst * x d.snd := by
    exact Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
      (g := SimpleGraph.Dart.edge)
      (fun d _ ↦ by simp) _
  calc
    ∑ e ∈ G.edgeFinset, 2 * symEdgeWeight x e =
        ∑ e ∈ G.edgeFinset,
          ∑ d ∈ (Finset.univ.filter fun d : G.Dart ↦ d.edge = e),
            x d.fst * x d.snd := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨u, v⟩ := e
      let d : G.Dart := ⟨(u, v), by simpa using he⟩
      change 2 * symEdgeWeight x s(u, v) =
        ∑ d' ∈ (Finset.univ.filter fun d' : G.Dart ↦ d'.edge = s(u, v)),
          x d'.fst * x d'.snd
      rw [show s(u, v) = d.edge by rfl, d.edge_fiber]
      rw [Finset.sum_pair (Ne.symm d.symm_ne)]
      change 2 * (x u * x v) = x u * x v + x v * x u
      ring
    _ = ∑ d : G.Dart, x d.fst * x d.snd := hfiber
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0 := by
      have hrhs :
          (∑ u : V, ∑ v : V, if G.Adj u v then x u * x v else 0) =
            ∑ uv : V × V,
              if G.Adj uv.1 uv.2 then x uv.1 * x uv.2 else 0 :=
        (Fintype.sum_prod_type (fun uv : V × V ↦
          if G.Adj uv.1 uv.2 then x uv.1 * x uv.2 else 0)).symm
      rw [hrhs]
      rw [← Finset.sum_filter]
      refine Finset.sum_bij'
        (fun d _ ↦ (d.fst, d.snd))
        (fun uv huv ↦ ⟨uv, (Finset.mem_filter.mp huv).2⟩)
        ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp
      · intro uv huv
        simp
      · intro d hd
        rfl
      · intro uv huv
        rcases uv with ⟨u, v⟩
        rfl
      · intro d hd
        rfl

omit [Fintype V] [DecidableEq V] in
/-- Balanced independent blow-up preserves clique-freeness. -/
theorem cliqueFree_balancedBlowup (G : SimpleGraph V) (k : ℕ) (_hk : 0 < k)
    (hG : G.CliqueFree 3) :
    (balancedBlowup G k).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
    SimpleGraph.is3Clique_iff.mp ht
  apply hG {a.1, b.1, c.1}
  rw [SimpleGraph.is3Clique_triple_iff]
  exact ⟨hab, hac, hbc⟩

omit [DecidableEq V] in
/-- Summing a profile inside each clone class transports its edge cost
exactly back to the original graph. -/
private lemma edgeCost_balancedBlowup
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (x : V × Fin k → ℚ) :
    edgeCost (balancedBlowup G k) x =
      edgeCost G (fun v ↦ ∑ i : Fin k, x (v, i)) := by
  classical
  apply (mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0))
  rw [two_mul_edgeCost_eq_ordered_sum,
    two_mul_edgeCost_eq_ordered_sum]
  simp only [Fintype.sum_prod_type, balancedBlowup_adj]
  rw [show
      (∑ u : V, ∑ i : Fin k, ∑ v : V, ∑ j : Fin k,
          if G.Adj u v then x (u, i) * x (v, j) else 0) =
        ∑ u : V, ∑ v : V, ∑ i : Fin k, ∑ j : Fin k,
          if G.Adj u v then x (u, i) * x (v, j) else 0 by
    apply Finset.sum_congr rfl
    intro u hu
    exact Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases huv : G.Adj u v
  · simp only [huv, if_true, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  · simp [huv]

omit [DecidableEq V] in
private lemma edgeCost_const
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℚ) :
    edgeCost G (fun _ ↦ a) =
      (G.edgeFinset.card : ℚ) * a ^ 2 := by
  classical
  rw [edgeCost_eq_sum_symEdgeWeight]
  have hweight : ∀ e : Sym2 V,
      symEdgeWeight (fun _ ↦ a) e = a ^ 2 := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v => simp [symEdgeWeight, pow_two]
  simp_rw [hweight]
  simp [nsmul_eq_mul]

omit [DecidableEq V] in
/-- A balanced `k`-fold blow-up has exactly `k²` copies of every edge. -/
theorem card_edgeFinset_balancedBlowup
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (balancedBlowup G k).edgeFinset.card =
      k ^ 2 * G.edgeFinset.card := by
  have hcost := edgeCost_balancedBlowup G k (fun _ ↦ 1)
  rw [edgeCost_const, edgeCost_const] at hcost
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcost
  norm_num [Nat.cast_pow, Nat.cast_mul] at hcost ⊢
  have hnat : (balancedBlowup G k).edgeFinset.card =
      G.edgeFinset.card * k ^ 2 := by
    exact_mod_cast hcost
  simpa [mul_comm] using hnat

omit [DecidableEq V] in
/-- The rational normalized edge density is invariant under every positive
balanced blow-up. -/
theorem edgeDensityQ_balancedBlowup
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k) :
    edgeDensityQ (balancedBlowup G k) = edgeDensityQ G := by
  unfold edgeDensityQ
  rw [card_edgeFinset_balancedBlowup]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow]
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · have hnQ : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp [hkQ, hnQ]

private lemma c4Hom_eq_ordered_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    c4Hom G =
      ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V,
        G.adjMatrix ℚ a b * G.adjMatrix ℚ b c *
          G.adjMatrix ℚ c d * G.adjMatrix ℚ d a := by
  unfold c4Hom Matrix.trace
  rw [show G.adjMatrix ℚ ^ 4 =
      G.adjMatrix ℚ * G.adjMatrix ℚ *
        G.adjMatrix ℚ * G.adjMatrix ℚ by noncomm_ring]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  let F : V → V → V → ℚ := fun b c d ↦
    G.adjMatrix ℚ a b * G.adjMatrix ℚ b c *
      G.adjMatrix ℚ c d * G.adjMatrix ℚ d a
  change (∑ d : V, ∑ c : V, ∑ b : V, F b c d) =
    ∑ b : V, ∑ c : V, ∑ d : V, F b c d
  calc
    (∑ d : V, ∑ c : V, ∑ b : V, F b c d) =
        ∑ c : V, ∑ d : V, ∑ b : V, F b c d := Finset.sum_comm
    _ = ∑ c : V, ∑ b : V, ∑ d : V, F b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ b : V, ∑ c : V, ∑ d : V, F b c d := Finset.sum_comm

omit [DecidableEq V] in
private lemma sum_prod_fst (k : ℕ) (f : V → ℚ) :
    (∑ p : V × Fin k, f p.1) = (k : ℚ) * ∑ v : V, f v := by
  rw [Fintype.sum_prod_type]
  simp [nsmul_eq_mul, Finset.mul_sum]

omit [DecidableEq V] in
private lemma sum_four_prod_fst
    (k : ℕ) (F : V → V → V → V → ℚ) :
    (∑ a : V × Fin k, ∑ b : V × Fin k,
      ∑ c : V × Fin k, ∑ d : V × Fin k,
        F a.1 b.1 c.1 d.1) =
      (k : ℚ) ^ 4 * ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, F a b c d := by
  calc
    (∑ a : V × Fin k, ∑ b : V × Fin k,
      ∑ c : V × Fin k, ∑ d : V × Fin k, F a.1 b.1 c.1 d.1) =
        (k : ℚ) * ∑ a : V, ∑ b : V × Fin k,
          ∑ c : V × Fin k, ∑ d : V × Fin k, F a b.1 c.1 d.1 :=
      sum_prod_fst k (fun a ↦ ∑ b : V × Fin k,
        ∑ c : V × Fin k, ∑ d : V × Fin k, F a b.1 c.1 d.1)
    _ = (k : ℚ) * ((k : ℚ) * ∑ a : V, ∑ b : V,
          ∑ c : V × Fin k, ∑ d : V × Fin k, F a b c.1 d.1) := by
      apply congrArg (fun z : ℚ ↦ (k : ℚ) * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_prod_fst k (fun b ↦
        ∑ c : V × Fin k, ∑ d : V × Fin k, F a b c.1 d.1)
    _ = (k : ℚ) * ((k : ℚ) * ((k : ℚ) * ∑ a : V, ∑ b : V,
          ∑ c : V, ∑ d : V × Fin k, F a b c d.1)) := by
      apply congrArg (fun z : ℚ ↦ (k : ℚ) * ((k : ℚ) * z))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      exact sum_prod_fst k (fun c ↦
        ∑ d : V × Fin k, F a b c d.1)
    _ = (k : ℚ) * ((k : ℚ) * ((k : ℚ) * ((k : ℚ) *
          ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, F a b c d))) := by
      apply congrArg (fun z : ℚ ↦
        (k : ℚ) * ((k : ℚ) * ((k : ℚ) * z)))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_prod_fst k (fun d ↦ F a b c d)
    _ = (k : ℚ) ^ 4 * ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, F a b c d := by
      ring

/-- The labelled four-cycle homomorphism count scales by `k⁴`. -/
theorem c4Hom_balancedBlowup
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    c4Hom (balancedBlowup G k) = (k : ℚ) ^ 4 * c4Hom G := by
  rw [c4Hom_eq_ordered_sum, c4Hom_eq_ordered_sum]
  simp only [SimpleGraph.adjMatrix_apply, balancedBlowup_adj]
  let F : V → V → V → V → ℚ := fun a b c d ↦
    (((if G.Adj a b then 1 else 0) * if G.Adj b c then 1 else 0) *
      if G.Adj c d then 1 else 0) * if G.Adj d a then 1 else 0
  change (∑ a : V × Fin k, ∑ b : V × Fin k,
      ∑ c : V × Fin k, ∑ d : V × Fin k, F a.1 b.1 c.1 d.1) =
    (k : ℚ) ^ 4 * ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, F a b c d
  exact sum_four_prod_fst k F

/-- The normalized labelled `C₄` homomorphism density is invariant under
every positive balanced blow-up. -/
theorem c4DensityQ_balancedBlowup
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k) :
    c4DensityQ (balancedBlowup G k) = c4DensityQ G := by
  unfold c4DensityQ
  rw [c4Hom_balancedBlowup]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · have hnQ : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp [hkQ, hnQ]

/-- Lift a profile by making it constant on each clone class. -/
private def liftProfile (k : ℕ) (x : V → ℚ) : V × Fin k → ℚ :=
  fun p ↦ x p.1

/-- Average a profile over every clone class. -/
private def averageProfile (k : ℕ) (x : V × Fin k → ℚ) : V → ℚ :=
  fun v ↦ (∑ i : Fin k, x (v, i)) / (k : ℚ)

omit [DecidableEq V] in
private lemma edgeCost_averageProfile
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (x : V × Fin k → ℚ) :
    edgeCost G (averageProfile k x) =
      edgeCost (balancedBlowup G k) x / (k : ℚ) ^ 2 := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [show averageProfile k x =
      fun v ↦ (1 / (k : ℚ)) * ∑ i : Fin k, x (v, i) by
    funext v
    simp [averageProfile, div_eq_mul_inv, mul_comm]]
  rw [edgeCost_smul, ← edgeCost_balancedBlowup]
  field_simp [hkQ]

omit [Fintype V] [DecidableEq V] in
private lemma averageProfile_liftProfile
    (k : ℕ) (hk : 0 < k) (x : V → ℚ) :
    averageProfile k (liftProfile k x) = x := by
  funext v
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [averageProfile, liftProfile, nsmul_eq_mul, hkQ]

omit [DecidableEq V] in
private lemma normalizedEdgeCostQ_averageProfile
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (x : V × Fin k → ℚ) :
    normalizedEdgeCostQ G (averageProfile k x) =
      normalizedEdgeCostQ (balancedBlowup G k) x := by
  unfold normalizedEdgeCostQ
  rw [edgeCost_averageProfile G k hk x]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · have hnQ : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp [hkQ, hnQ]

omit [DecidableEq V] in
private lemma normalizedEdgeCostQ_liftProfile
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (x : V → ℚ) :
    normalizedEdgeCostQ (balancedBlowup G k) (liftProfile k x) =
      normalizedEdgeCostQ G x := by
  rw [← normalizedEdgeCostQ_averageProfile G k hk]
  rw [averageProfile_liftProfile k hk]

omit [DecidableEq V] in
private lemma isFractionalHalf_liftProfile
    (k : ℕ) (x : V → ℚ) (hx : IsFractionalHalf x) :
    IsFractionalHalf (liftProfile k x) := by
  constructor
  · intro p
    exact hx.1 p.1
  · rw [show (∑ p : V × Fin k, liftProfile k x p) =
        (k : ℚ) * ∑ v : V, x v by
      exact sum_prod_fst k x]
    rw [hx.2]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring

omit [DecidableEq V] in
private lemma isFractionalHalf_averageProfile
    (k : ℕ) (hk : 0 < k) (x : V × Fin k → ℚ)
    (hx : IsFractionalHalf x) :
    IsFractionalHalf (averageProfile k x) := by
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  constructor
  · intro v
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun i _ ↦ (hx.1 (v, i)).1) hkQ.le
    · apply (div_le_one hkQ).2
      calc
        (∑ i : Fin k, x (v, i)) ≤ ∑ _i : Fin k, (1 : ℚ) :=
          Finset.sum_le_sum fun i _ ↦ (hx.1 (v, i)).2
        _ = (k : ℚ) := by simp
  · calc
      (∑ v : V, averageProfile k x v) =
          (∑ v : V, ∑ i : Fin k, x (v, i)) / (k : ℚ) := by
        simp [averageProfile, Finset.sum_div]
      _ = ((Fintype.card (V × Fin k) : ℚ) / 2) / (k : ℚ) := by
        rw [← hx.2, Fintype.sum_prod_type]
      _ = (Fintype.card V : ℚ) / 2 := by
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        field_simp [ne_of_gt hkQ]

omit [DecidableEq V] in
/-- Existence of a fractional half below a normalized rational threshold is
exactly invariant under positive balanced blow-up. -/
theorem hasNormalizedFractionalHalfBoundQ_balancedBlowup_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (B : ℚ) :
    HasNormalizedFractionalHalfBoundQ (balancedBlowup G k) B ↔
      HasNormalizedFractionalHalfBoundQ G B := by
  constructor
  · rintro ⟨x, hx, hcost⟩
    refine ⟨averageProfile k x, isFractionalHalf_averageProfile k hk x hx, ?_⟩
    rwa [normalizedEdgeCostQ_averageProfile G k hk x]
  · rintro ⟨x, hx, hcost⟩
    refine ⟨liftProfile k x, isFractionalHalf_liftProfile k x hx, ?_⟩
    rwa [normalizedEdgeCostQ_liftProfile G k hk x]

/-- The fractional internal-edge objective associated to a two-colouring. -/
private def internalProfileCost
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) : ℚ :=
  edgeCost G x + edgeCost G (fun v ↦ 1 - x v)

private lemma edgeCost_update_affine
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) (v : V) :
    edgeCost G x =
      x v * edgeCost G (Function.update x v 1) +
        (1 - x v) * edgeCost G (Function.update x v 0) := by
  classical
  rw [edgeCost_eq_sum_symEdgeWeight, edgeCost_eq_sum_symEdgeWeight,
    edgeCost_eq_sum_symEdgeWeight]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u w =>
      have huw : G.Adj u w := by simpa using he
      by_cases hu : u = v <;> by_cases hw : w = v
      · subst u
        subst w
        exact False.elim (huw.ne rfl)
      · simp [symEdgeWeight, hu, hw]
      · simp [symEdgeWeight, hu, hw]; ring
      · simp [symEdgeWeight, hu, hw]; ring

private lemma internalProfileCost_update_affine
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ) (v : V) :
    internalProfileCost G x =
      x v * internalProfileCost G (Function.update x v 1) +
        (1 - x v) * internalProfileCost G (Function.update x v 0) := by
  have hcompl0 :
      Function.update (fun w ↦ 1 - x w) v 1 =
        fun w ↦ 1 - Function.update x v 0 w := by
    funext w
    by_cases hw : w = v <;> simp [Function.update, hw]
  have hcompl1 :
      Function.update (fun w ↦ 1 - x w) v 0 =
        fun w ↦ 1 - Function.update x v 1 w := by
    funext w
    by_cases hw : w = v <;> simp [Function.update, hw]
  unfold internalProfileCost
  rw [edgeCost_update_affine G x v,
    edgeCost_update_affine G (fun w ↦ 1 - x w) v]
  rw [hcompl0, hcompl1]
  ring

omit [DecidableEq V] in
private lemma exists_internal_coordinate_rounding
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ)
    (hx : ∀ w, 0 ≤ x w ∧ x w ≤ 1) (v : V) :
    ∃ y : V → ℚ,
      (∀ w, 0 ≤ y w ∧ y w ≤ 1) ∧
      (y v = 0 ∨ y v = 1) ∧
      internalProfileCost G y ≤ internalProfileCost G x ∧
      ∀ w, w ≠ v → y w = x w := by
  classical
  let x0 := Function.update x v 0
  let x1 := Function.update x v 1
  have hx0 : ∀ w, 0 ≤ x0 w ∧ x0 w ≤ 1 := by
    intro w
    by_cases hw : w = v
    · subst w
      simp [x0]
    · simpa [x0, Function.update_of_ne hw] using hx w
  have hx1 : ∀ w, 0 ≤ x1 w ∧ x1 w ≤ 1 := by
    intro w
    by_cases hw : w = v
    · subst w
      simp [x1]
    · simpa [x1, Function.update_of_ne hw] using hx w
  have haff := internalProfileCost_update_affine G x v
  by_cases hle : internalProfileCost G x1 ≤ internalProfileCost G x0
  · refine ⟨x1, hx1, Or.inr (by simp [x1]), ?_, ?_⟩
    · have hnonneg :
          0 ≤ (1 - x v) *
            (internalProfileCost G x0 - internalProfileCost G x1) :=
        mul_nonneg (sub_nonneg.mpr (hx v).2) (sub_nonneg.mpr hle)
      dsimp [x0, x1] at haff ⊢
      nlinarith
    · intro w hw
      simp [x1, Function.update_of_ne hw]
  · have hle' : internalProfileCost G x0 ≤ internalProfileCost G x1 :=
      le_of_not_ge hle
    refine ⟨x0, hx0, Or.inl (by simp [x0]), ?_, ?_⟩
    · have hnonneg :
          0 ≤ x v *
            (internalProfileCost G x1 - internalProfileCost G x0) :=
        mul_nonneg (hx v).1 (sub_nonneg.mpr hle')
      dsimp [x0, x1] at haff ⊢
      nlinarith
    · intro w hw
      simp [x0, Function.update_of_ne hw]

omit [DecidableEq V] in
private lemma exists_internal_rounding_on
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (x : V → ℚ) (hx : ∀ w, 0 ≤ x w ∧ x w ≤ 1) :
    ∃ y : V → ℚ,
      (∀ w, 0 ≤ y w ∧ y w ≤ 1) ∧
      (∀ w ∈ S, y w = 0 ∨ y w = 1) ∧
      internalProfileCost G y ≤ internalProfileCost G x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨x, hx, by simp, le_rfl⟩
  | @insert v S hv ih =>
      obtain ⟨y, hy, hyint, hycost⟩ := ih
      obtain ⟨z, hz, hzv, hzcost, hzother⟩ :=
        exists_internal_coordinate_rounding G y hy v
      refine ⟨z, hz, ?_, hzcost.trans hycost⟩
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact hzv
      · rw [hzother w (by rintro rfl; exact hv hw)]
        exact hyint w hw

private lemma internalProfileCost_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    internalProfileCost G (finsetIndicator S) =
      ((edgeCountOn G S + edgeCountOn G Sᶜ : ℕ) : ℚ) := by
  have hcompl : (fun v ↦ 1 - finsetIndicator S v) =
      finsetIndicator Sᶜ := by
    funext v
    by_cases hv : v ∈ S <;> simp [finsetIndicator, hv]
  unfold internalProfileCost
  rw [hcompl, edgeCost_finsetIndicator, edgeCost_finsetIndicator]
  norm_num

private lemma exists_integral_internal_profile
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℚ)
    (hx : ∀ w, 0 ≤ x w ∧ x w ≤ 1) :
    ∃ S : Finset V,
      ((edgeCountOn G S + edgeCountOn G Sᶜ : ℕ) : ℚ) ≤
        internalProfileCost G x := by
  obtain ⟨y, hy, hyint, hycost⟩ :=
    exists_internal_rounding_on G Finset.univ x hx
  let S : Finset V := Finset.univ.filter fun v ↦ y v = 1
  have hy_indicator : y = finsetIndicator S := by
    funext v
    have hv := hyint v (Finset.mem_univ v)
    rcases hv with hv | hv
    · simp [S, finsetIndicator, hv]
    · simp [S, finsetIndicator, hv]
  refine ⟨S, ?_⟩
  rw [← internalProfileCost_indicator G S, ← hy_indicator]
  exact hycost

/-- Lift a cut by placing every clone on the same side as its original
vertex. -/
private def liftCut (k : ℕ) (S : Finset V) : Finset (V × Fin k) :=
  S.product Finset.univ

omit [Fintype V] in
private lemma averageProfile_indicator_liftCut
    (k : ℕ) (hk : 0 < k) (S : Finset V) :
    averageProfile k (finsetIndicator (liftCut k S)) =
      finsetIndicator S := by
  funext v
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hv : v ∈ S
  · simp [averageProfile, liftCut, finsetIndicator, hv,
      nsmul_eq_mul, hkQ]
  · simp [averageProfile, liftCut, finsetIndicator, hv]

private lemma averageProfile_indicator_compl
    (k : ℕ) (hk : 0 < k) (T : Finset (V × Fin k)) :
    (fun v ↦ 1 - averageProfile k (finsetIndicator T) v) =
      averageProfile k (finsetIndicator Tᶜ) := by
  funext v
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpoint : ∀ i : Fin k,
      finsetIndicator Tᶜ (v, i) = 1 - finsetIndicator T (v, i) := by
    intro i
    by_cases hi : (v, i) ∈ T <;> simp [finsetIndicator, hi]
  unfold averageProfile
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp [hkQ]

private lemma internalProfileCost_average_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (T : Finset (V × Fin k)) :
    internalProfileCost G
        (averageProfile k (finsetIndicator T)) =
      ((edgeCountOn (balancedBlowup G k) T +
          edgeCountOn (balancedBlowup G k) Tᶜ : ℕ) : ℚ) /
        (k : ℚ) ^ 2 := by
  unfold internalProfileCost
  rw [averageProfile_indicator_compl k hk T]
  rw [edgeCost_averageProfile G k hk,
    edgeCost_averageProfile G k hk]
  rw [edgeCost_finsetIndicator, edgeCost_finsetIndicator]
  norm_num
  ring

private lemma normalizedInternalCutCostQ_eq_internalProfileCost_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    normalizedInternalCutCostQ G S =
      internalProfileCost G (finsetIndicator S) /
        (Fintype.card V : ℚ) ^ 2 := by
  unfold normalizedInternalCutCostQ
  rw [internalProfileCost_indicator]

private lemma normalizedInternalCutCostQ_balancedBlowup_eq_average
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (T : Finset (V × Fin k)) :
    normalizedInternalCutCostQ (balancedBlowup G k) T =
      internalProfileCost G
          (averageProfile k (finsetIndicator T)) /
        (Fintype.card V : ℚ) ^ 2 := by
  unfold normalizedInternalCutCostQ
  rw [internalProfileCost_average_indicator G k hk T]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · have hnQ : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp [hkQ, hnQ]

omit [Fintype V] in
private lemma averageProfile_indicator_bounds
    (k : ℕ) (hk : 0 < k) (T : Finset (V × Fin k)) :
    ∀ v, 0 ≤ averageProfile k (finsetIndicator T) v ∧
      averageProfile k (finsetIndicator T) v ≤ 1 := by
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  intro v
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg fun i _ ↦ by
        by_cases hi : (v, i) ∈ T <;> simp [finsetIndicator, hi]
    · exact hkQ.le
  · apply (div_le_one hkQ).2
    calc
      (∑ i : Fin k, finsetIndicator T (v, i)) ≤
          ∑ _i : Fin k, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hit : (v, i) ∈ T <;> simp [finsetIndicator, hit]
      _ = (k : ℚ) := by simp

/-- Existence of a cut below a normalized rational internal-edge threshold is
exactly invariant under positive balanced blow-up. -/
theorem hasNormalizedInternalCutBoundQ_balancedBlowup_iff
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 0 < k)
    (B : ℚ) :
    HasNormalizedInternalCutBoundQ (balancedBlowup G k) B ↔
      HasNormalizedInternalCutBoundQ G B := by
  constructor
  · rintro ⟨T, hT⟩
    let x := averageProfile k (finsetIndicator T)
    obtain ⟨S, hS⟩ := exists_integral_internal_profile G x
      (averageProfile_indicator_bounds k hk T)
    refine ⟨S, ?_⟩
    rw [normalizedInternalCutCostQ_eq_internalProfileCost_indicator]
    rw [normalizedInternalCutCostQ_balancedBlowup_eq_average G k hk T] at hT
    by_cases hn : Fintype.card V = 0
    · simpa [hn] using hT
    · have hnQ : (0 : ℚ) < (Fintype.card V : ℚ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hdiv :
          internalProfileCost G (finsetIndicator S) /
              (Fintype.card V : ℚ) ^ 2 ≤
            internalProfileCost G x /
              (Fintype.card V : ℚ) ^ 2 := by
        apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hnQ)).2
        rwa [internalProfileCost_indicator]
      exact hdiv.trans hT
  · rintro ⟨S, hS⟩
    refine ⟨liftCut k S, ?_⟩
    rw [normalizedInternalCutCostQ_balancedBlowup_eq_average G k hk]
    rw [averageProfile_indicator_liftCut k hk S]
    rwa [← normalizedInternalCutCostQ_eq_internalProfileCost_indicator]

end

end Erdos128
