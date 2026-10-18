import Erdos128.GraphBasics

set_option linter.style.header false

/-!
# Rational normalizations for finite graphs

The constructive part of the sparse-half proof stays over `Rat`.  This module
collects the normalized quantities and threshold predicates shared by the
anchor, cut, and balanced-blow-up arguments.
-/

namespace Erdos128

open scoped BigOperators

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The rational normalized quadratic cost of a vertex profile. -/
def normalizedEdgeCostQ (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℚ) : ℚ :=
  edgeCost G x / (Fintype.card V : ℚ) ^ 2

/-- A rational fractional half with normalized cost at most `B`. -/
def HasNormalizedFractionalHalfBoundQ
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℚ) : Prop :=
  ∃ x : V → ℚ, IsFractionalHalf x ∧ normalizedEdgeCostQ G x ≤ B

/-- The normalized number of edges internal to the two sides of a cut. -/
def normalizedInternalCutCostQ
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℚ :=
  ((edgeCountOn G S + edgeCountOn G Sᶜ : ℕ) : ℚ) /
    (Fintype.card V : ℚ) ^ 2

/-- A cut whose normalized internal-edge count is at most `B`. -/
def HasNormalizedInternalCutBoundQ
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : ℚ) : Prop :=
  ∃ S : Finset V, normalizedInternalCutCostQ G S ≤ B

omit [DecidableEq V] in
lemma normalizedEdgeCostQ_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V → ℚ} (hx : ∀ v, 0 ≤ x v) :
    0 ≤ normalizedEdgeCostQ G x := by
  unfold normalizedEdgeCostQ
  exact div_nonneg (edgeCost_nonneg G hx) (sq_nonneg _)

lemma normalizedInternalCutCostQ_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    0 ≤ normalizedInternalCutCostQ G S := by
  unfold normalizedInternalCutCostQ
  positivity

end

end Erdos128
