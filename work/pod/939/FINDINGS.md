# Lane 939 findings (number theorist, Claude Fable; agent stopped 01:26 on a resume error)

Bounded, exhaustive negatives. No new solution and no family. Details: NOTES.md.

- **r = 5:** an exhaustive meet-in-the-middle search over all 5-full numbers (no coprimality
  pruning) finds only the two known primitive solutions (Cambie, Kitamura) through **D ≤ 1e22**
  (`runs/mitm5_1e22.err` and `.out`: `DONE N=10000000000000000000000 n=329544 sol=6 dup=3480470 noncop=359625897`,
  where the 6 hits are the 2 primitive solutions and their $2^5$- and $3^5$-scaled copies). This closes
  the case Cambie left open below 1e16 (all pairwise gcds > 1, joint gcd 1) and extends the unconditional
  exhaustive bound 100× beyond 1e20.
- **r = 6 (infinite family, Lean-checked):** `lean/ErdosLab/Erdos939.lean` proves
  `Erdos939.erdos_939.variants.finite` (`¬ ∀ r ≥ 4, (Erdos939Sums r).Finite`) in Lean 4 with
  standard axioms only via the explicit polynomial family $Y = 2^4 \cdot 3^5 \cdot 5^6$,
  $X_k = (30(k+1)+1)^6$ in $(X_k + Y)^6 = (X_k - Y)^6 + 12 X_k^5 Y + 40 X_k^3 Y^3 + 12 X_k Y^5$.
- **r = 4:** no coprime a + b = c with all terms 4-full and c ≤ 1e20 (815,514 4-full numbers).
  Cambie's published bound was 1e14.
- **Geometry:** a complete classification of degree-5 genus-1 orbifold curves finds none over Q.
  Over Q(√5) there is exactly one, the golden-ratio curve E_φ, with the identity
  φ³ − φ² s_P + φ s_{2P} + s_{3P} = 0. The rational genus-1 quartics on the twisted Fermat quintics
  sit on planes that rule out positive solutions. The "Cohn surfaces" through the two known
  solutions have no other point with |coords| ≤ 40000 (both surfaces, `runs/surf5_*_H40000.err`).
- **Heuristic:** about 1.2 coprime solutions expected below 1e18 (2 observed), with a tail of
  0.2–0.4 beyond. The evidence leans toward finitely many solutions for r = 5.
- **Degree-10 antisymmetric genus-1 curves (orphaned run, finished 01:54):** every non-degenerate
  solution found has d irrational, with minimal polynomial d² + 4d − 1 (so d ∈ Q(√5)), or d
  complex. None is rational, matching the degree-5 classification. `runs/hyperosc10_num.log`.
