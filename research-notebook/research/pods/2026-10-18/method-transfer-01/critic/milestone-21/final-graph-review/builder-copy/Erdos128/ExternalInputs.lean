import Erdos128.GraphBasics

set_option linter.style.header false

/-!
# External finite-graph inputs for the sparse-half proof

This file records the two results used from outside the elementary
`131 / 5000` argument.  They are transparent propositions about a fixed
finite graph, not axioms: later theorems must receive proofs of them as
explicit hypotheses.
-/

namespace Erdos128

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The conclusion of the Balogh--Clemen--Lidický max-cut input for a
particular finite graph.  The witness `X` is one side of the cut, and the
left-hand side counts the edges internal to its two sides. -/
def BCLCutCertificate (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ X : Finset V,
    ((edgeCountOn G X + edgeCountOn G Xᶜ : ℕ) : ℚ) ≤
      (2 / 47 : ℚ) * (Fintype.card V : ℚ) ^ 2

/-- The exact rational coefficient in the certified `C₄` inequality. -/
def c4FlagGamma : ℚ :=
  3 / 64 + 1 / 50000000000

/-- The number of homomorphisms from the labelled four-cycle to `G`,
represented as the trace of the fourth power of the adjacency matrix. -/
def c4Hom (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  Matrix.trace ((G.adjMatrix ℚ) ^ 4)

/-- The normalized edge density `2e(G) / |V(G)|²`, valued in the rationals. -/
def edgeDensityQ (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  2 * (G.edgeFinset.card : ℚ) / (Fintype.card V : ℚ) ^ 2

/-- The normalized four-cycle homomorphism density
`hom(C₄, G) / |V(G)|⁴`, valued in the rationals. -/
def c4DensityQ (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  c4Hom G / (Fintype.card V : ℚ) ^ 4

/-- The conclusion of the flag-algebra `C₄` input for a particular
finite graph, with all powers of the graph order cleared from denominators.

Writing `n = |V|`, `m = e(G)`, and `H₄ = hom(C₄, G)`, this is
`n² H₄ ≥ 8m³ - 2 γ m n⁴`.  For `n > 0`, division by `n⁶`
recovers `t(C₄,G) ≥ r³ - γr` with `r = 2m/n²`. -/
def C4FlagCertificate (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  let n : ℚ := Fintype.card V
  let m : ℚ := G.edgeFinset.card
  n ^ 2 * c4Hom G ≥
    8 * m ^ 3 - 2 * c4FlagGamma * m * n ^ 4

/-- For a nonempty finite vertex type, the denominator-cleared flag
certificate implies its normalized density form. -/
theorem c4DensityQ_ge_of_C4FlagCertificate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 0 < Fintype.card V) (hcert : C4FlagCertificate G) :
    c4DensityQ G ≥
      edgeDensityQ G ^ 3 - c4FlagGamma * edgeDensityQ G := by
  have hn : (0 : ℚ) < (Fintype.card V : ℚ) := by
    exact_mod_cast hcard
  simp only [C4FlagCertificate] at hcert
  unfold c4DensityQ edgeDensityQ
  field_simp [ne_of_gt hn]
  ring_nf at hcert ⊢
  exact hcert

end

end Erdos128
