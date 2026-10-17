# Erdős 834 (part ii): a 3-chromatic-critical 3-graph with minimum degree 7

Source: https://www.erdosproblems.com/834 · FC: `Erdos834.erdos_834.parts.ii`
(FormalConjectures/ErdosProblems/834.lean @ d9ce556) · Li, arXiv:2512.24850.

## Why
- Formalization effort 1/5 in `data/erdos/formalize.csv`; FC already has the statement, with a
  concrete answer (an existential, no `answer(sorry)`).
- The answer is witnessed by one explicit 9-vertex, 22-edge hypergraph (Li 2025, Section 4.1), so
  every fact is a finite check that kernel `decide` can do; no Mathlib gaps.
- Good pilot for the challenge/solution contract: small, fully decidable, default axiom tier.

## Statement review
FC statement (copied verbatim into `erdos/Challenge/Erdos834.lean`):
`∃ n (H : Finset (Finset (Fin n))), H.IsUniform 3 ∧ H.HasHypergraphChromaticNumber 3 ∧
(∀ e ∈ H, (H.erase e).HypergraphColorable 2) ∧
(∀ v, (H.filter (v ∉ ·)).HypergraphColorable 2) ∧ ∀ v, 7 ≤ H.hypergraphDegree v`.

Compared with Li's Theorem (chromatic interpretation): χ(H) = 3, H − e and H − v are 2-colourable
for every edge e and vertex v, δ(H) ≥ 7, H 3-uniform on 9 vertices.
- Colouring notion: FC `HypergraphColorable k` = some `c : V → Fin k` with no monochromatic edge
  (weak colouring). Same as Li's.
- `HasHypergraphChromaticNumber 3` = 3-colourable and not j-colourable for j < 3. Matches χ = 3.
- Vertex deletion is modelled as "drop the edges through v" while still colouring all of `Fin n`.
  Equivalent to colouring H − v, because v lies in no remaining edge and can take any colour.
- Degree is over the whole ground type `Fin n`, so isolated vertices are not allowed. That only
  makes the statement stronger, and Li's H has no isolated vertices.
- Not vacuous: n = 0 forces H = ∅, which is 0-colourable, so `HasHypergraphChromaticNumber 3`
  fails; a witness must be a genuine hypergraph.
- **Interpretation caveat (for the human approver):** erdosproblems.com/834 is answered differently
  under the two meanings of "3-critical". FC part i (transversal criticality) is answered *no* by Li;
  part ii (chromatic criticality, edge- *and* vertex-critical) is answered *yes*. This pilot
  proves part ii only. FC's part ii asks for edge- and vertex-criticality together, which is at least
  as strong as the usual chromatic "3-critical" (edge-criticality) reading. No discrepancy with the
  source result was found.

## Blueprint (lemma DAG)
All nodes are *search* (explicit witness), checked by kernel `decide +kernel`.
- `liH` : Li's 22 edges, relabelled 1..9 ↦ 0..8. Re-verified independently in Python before use.
- `liH_uniform` (decide) ; `liH_degree` (decide; degrees are 10,7,7,7,7,7,7,7,7)
- `liH_colorable_three` : witness colouring `![0,0,1,0,0,1,2,1,1]` (decide)
- `liH_not_colorable_zero` (`Fin 0` is empty), `liH_not_colorable_one` (an edge is monochromatic)
- `liH_not_colorable_two` : `Fin.forall_fin_succ_pi` unrolls the 2^9 colourings, then decide
- `liH_edge_critical` : table `edgeWit : Fin 22 → Fin 9 → Fin 2`; decide `∀ e ∈ H, ∃ i, proper`
- `liH_vertex_critical` : table `vertWit : Fin 9 → Fin 9 → Fin 2`; decide
- `solution` : assemble with n = 9.

Status: proof complete (90 lines). `erdos/scripts/check.sh 834` is green. Waiting for statement approval.
