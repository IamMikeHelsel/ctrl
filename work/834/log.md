# Log: Erdős 834

- 2026-10-17 · Claude Code (pilot). Picked 834 part ii over 1213/895/915/473/346/440: it is the only
  candidate whose whole proof is a finite, kernel-decidable witness check. Pulled Li's edge list from
  arXiv:2512.24850 (HTML, Section 4.1 / Appendix A). Re-checked it with a throwaway Python
  brute force: 22 edges, degrees [10,7×8], not 2-colourable, 3-colourable, every edge/vertex deletion
  2-colourable. The witness colourings were recomputed rather than copied.
- Wrote `lean/Challenge/Erdos834.lean` (verbatim FC part ii, `approved-by: (pending)`) and
  `lean/ErdosLab/Erdos834.lean`. All lemmas close by `decide +kernel` on the first try. The file
  compiles in about 50 s.
- `lean/scripts/check.sh 834`: build, tokens, axioms (propext, Classical.choice, Quot.sound) and
  binding all ok. Phase stays `draft` until a human approves the statement.

## Verifier report 2026-10-17
Checks: mac pass except NOT_APPROVED (`ctrl check 834 --json` exit 3: build ok, tokens ok, axioms ok, binding ok, hash "challenge not approved"); spark pass except NOT_APPROVED (`ctrl spark check 834 --json` on sparky.local, exit 3, same five results). Exit 3 is expected while the challenge is a draft.
Checklist:
1 binding: pass. `#check @Challenge.Erdos834.solution` gives `Challenge.Erdos834.statement`. The CLI reports binding "(Expr.const), statement : Prop". `solution` is a term proof of `statement` itself, not a restatement.
2 def drift: pass. The Challenge body is identical to FC `erdos_834.parts.ii` @ d9ce556 (checked against .lake/packages/formal_conjectures, HEAD d9ce556af8). A grep of ErdosLab/Erdos834.lean for instance|notation|macro|elab|attribute|@[simp|set_option|local finds no hits; the only match, on "axiom", is in the docstring. Only private defs (liH, edgeWit, vertWit) and lemmas were added, and none of them is a statement dependency. The hash cannot be checked until approval. git log shows the Challenge file has one commit (4a94d15).
3 axioms: pass. `#print axioms solution` gives [propext, Classical.choice, Quot.sound], and that covers every helper transitively. No sorry, native_decide, opaque, implemented_by or extern. The tier is default.
4 vacuity: pass. The statement is an existential, so the risk is a trivially satisfiable statement, not a trivially true universal. The FC defs were probed in Lean (/tmp/p834.lean). A single 3-edge is 2-colourable, so it fails `HasHypergraphChromaticNumber 3`. The constant colouring is not proper, so "proper" means no monochromatic edge. Degree counts the edges through v (2 and 1 in a test case). n = 0 gives H = ∅, which is 0-colourable, so the χ = 3 clause rules it out. With `IsUniform 3` all edges have exactly 3 vertices, so empty or singleton edges cannot be used to make the hypergraph uncolourable. The witness has to be a genuinely non-2-colourable 3-graph.
5 misread statement: pass. I re-derived the problem from erdosproblems.com/834 and the arXiv:2512.24850 abstract. The problem leaves "3-critical" undefined. Under the transversal notion the answer is no (FC part i). Under the chromatic notion (χ = 3, and deleting any edge or any vertex makes it 2-colourable) the answer is yes, via Li's 9-vertex example. The FC definitions in FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean match:
   - `IsProperHypergraphColoring`: every edge has x, y with c x ≠ c y (weak colouring).
   - `HypergraphColorable k`: there exists c : V → Fin k that is proper.
   - `HasHypergraphChromaticNumber k`: colourable with k and not with any j < k, which is χ = k.
   - `hypergraphDegree v`: #{e ∈ H | v ∈ e}.
   - `IsUniform r`: every edge has card r.
   Vertex deletion is modelled by `filter (v ∉ ·)`, which colours all of Fin n. That is equivalent, because v is then isolated. The degree bound ranges over all of Fin n, which is stronger than the paper's δ ≥ 7. The proof proves part ii only (chromatic reading), and plan.md flags this for the approver.
6 certificates: pass. Every finite fact is closed by `decide +kernel` in Lean; no solver output is trusted. As a cross-check I wrote my own Python brute force (/tmp/v834.py), separate from the prover's. It found 22 distinct edges, degrees [10,7,7,7,7,7,7,7,7], not 2-colourable, 3-colourable, and every edge deletion and every vertex deletion 2-colourable.
7 env: pass. It builds on mac (lake, about 47 s) and on sparky.local. Note: `ctrl spark sync` also pushed another agent's in-progress src/ctrl/tests files, but the 834 result does not depend on them.
Verdict: VERIFIED (proof is sound and binds to the draft statement; the statement still needs human approval, `ctrl approve 834 --by <name>`)
Failure: none. The only open item is NOT_APPROVED, which is a human step: the statement review in plan.md has to be accepted, including the part-ii-only interpretation caveat.
