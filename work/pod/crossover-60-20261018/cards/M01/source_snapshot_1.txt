# Interdisciplinary pod — shared brief (2026-10-18)

AI-written working notes. Every result here is a candidate until a Lean file checks it.

## Rules for every pod member
- Write only inside `work/pod/<lane>/`. Never edit `lean/Challenge/`.
- Every claimed hit gets an independent exact-integer re-check script (no floats) and a line in
  `work/pod/<lane>/NOTES.md`: what was tried, ranges, result, and negative results too.
- Python: `uv run --with <pkg> python script.py` (no global pip). C/Rust are fine for hot loops.
- Prior art matters. Read the linked forum threads before claiming anything is new.

## Lane 885: common factor differences (open for k ≥ 5)
FC: `Erdos885.erdos_885` (lean/.lake/packages/formal_conjectures/FormalConjectures/ErdosProblems/885.lean).
`d ∈ D(N)` iff `4N + d²` is a perfect square (then `N = b(b+d)`, `b = (s-d)/2`).

**Grid form.** Case k is equivalent to an (k+1)×k rational grid `U+V ⊆ squares`
(`u_i + v_j = s_ij²` for all i,j). The grid problem is symmetric in rows/columns. Normalising by a
row gives K_{m-1,n} in the bipartite graph {N} – {d} (edge iff d ∈ D(N)); normalising by a column
gives K_{n-1,m}. So for an m×n grid:

| grid | integer form A | integer form B | status (forum, Oct 2026) |
| --- | --- | --- | --- |
| 5×4 | 4 N's share 4 d's (k=4) | 3 N's share 5 d's | known (Bremner 2019; Mausberg; Pan; Aleksanndr) |
| **5×5** | 4 N's share 5 d's | same | **unknown: new stepping stone** |
| 6×4 | 5 N's share 4 d's | 3 N's share 6 d's | known (community list of 71, erdosproblemaday.com, Jul 2026); pod rediscovered 2 classes, Lean-checked |
| **6×5** | **5 N's share 5 d's (solves k=5)** | **4 N's share 6 d's** | **open** |

Transposition recipe (form B → form A): rows {0, 4N_1..4N_m}, columns {d_j²}; transpose, subtract
the smallest new row, scale by 4 if parities clash. Re-check the final integers directly.

Prior art to read first: https://www.erdosproblems.com/forum/thread/885 (Pan's 5×4 with
genus-13/Chabauty analysis and repo github.com/zoahdev/erdos885-square-sum; Mausberg
Y(756000,15971200,45130176) ⊇ {330,870,2445,4155,10482}; Aleksanndr's genus-1 row curves;
Choudhry arXiv:2508.07806 families (3,3),(5,3),(4,4)).
Known examples are smooth: 79200 = 2^5·3^2·5^2·11, 227205 = 3^5·5·11·17, 1258560 = 2^6·3^2·5·19·23.

Lean: a K_{5,5} witness closes `erdos_885` at k=5 exactly like the in-file proof of `k_eq_4`.
Ready-made: `python3 work/pod/885/gen_lean.py 5 "N1,..,N5" "d1,..,d5" > X.lean`, then
`cd lean && lake env lean ../X.lean` (tested at k=4 on Pan's grid: ~24 s, standard axioms only).
`work/pod/885/transpose_check.py` shows the grid → integer-form conversion.

## Lane MF-13: Byers–Nash for the Lyapunov operator (open at n = 6)
L_A(X) = AX + XAᵀ. Kressner–Vandereycken (arXiv 2608.20875, Aug 2026) give an exact n = 7
counterexample; Chen–Tian 2015 prove n ≤ 5. Status and derivations:
`~/dev/ctrl-research-notebook/research-notebook/research/mf13-next-step.txt`. A strict n = 6
counterexample needs full-rank coupled skew witnesses (rank ≤ 4 can't win, pending formal check).
Subdirs: `mf13/opt/` (numerical search), `mf13/theory/` (reductions + Lean). The theory member
writes `mf13/theory/REDUCED_SEARCH.md` for the optimizer to consume.

## Lane 939: r-powerful sums (open at r = 4 and r = 5)
FC: `Erdos939.erdos_939`. r=4: no example; Cambie: exhaustive, max(a,b) > 10^14. r=5: two
examples (Cambie, Kitamura); Cambie MITM: no others with d < 10^16 except pairwise-non-coprime ones.
Whether r=5 has infinitely many is open. r ≥ 6 is solved (binomial family), so it doesn't count.
Forum: https://www.erdosproblems.com/forum/thread/939
