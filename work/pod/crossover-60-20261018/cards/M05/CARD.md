# M05 — Lyapunov amplification in dimension six

**PM decision: GO for follow-up after all 60 initial reviews.** Completion and elapsed
research time are recorded in `../../state.json`; this card does not override that ledger.
AI-written by the root PM with independent domain, inventor and critic workers, all using
the inherited root model (exact runtime identifier unavailable).

## Question and provenance

For every real 6×6 A, does the Frobenius operator norm of L_A(X)=AX+XAᵀ on symmetric
matrices dominate its norm on skew matrices? The inspected
[Kressner–Vandereycken paper](https://arxiv.org/html/2608.20875v1) gives a dimension-seven
counterexample and leaves dimension six open. This session does not solve that question.

Starting sources are `work/pod/mf13/theory/REDUCED_SEARCH.md` and the notebook's audited
`research/mf13-next-step.txt`; exact absolute paths and hashes are in the frozen roster.
The former proposes three trace moments and an involution construction. The latter explicitly
leaves global compatibility open. Existing prototype code checks the full residual; we found
no demonstrated numerical acceptance bug.

## Crossovers

- Fredholm compatibility: use the full adjoint nullspace to certify consistency, retaining
  rank changes rather than assuming three independent moments.
- Critical camera configurations: generic dimension counts fail on degenerate strata.
  Nonorthogonal congruence preserves rank and solvability, not Frobenius norms.
- Robust control dual bounds: almost-lost constraints bound the size of every compatible
  solution, providing a cheap candidate rejection gate before optimization.
- Experimental design: choose fixed symmetric probes and minimize their output energy over
  the full compatible affine family. Bad probes are useful negative controls.

## Checked result

Let J=[[0,1],[-1,0]], K=diag(J,2J,J/2), Y=diag(J,J/2,2J). Then KY=YK=−I and both
squared Frobenius norms are 21/2. All moments tr((YK)^j(Y²−K²)) vanish, yet no real A
satisfies AK+KAᵀ=Y and AᵀY+YA=K. Entry (2,3) requires the same diagonal sum to equal
both 1/4 and 4. Joint unit normalization preserves the contradiction by hand scaling.

`RepeatedSpectrum.lean` compiles and the critic independently compiled identical source.
Five declarations check products, skewness/trace equality, absence of A, the zero reduced
map and all natural-number moments. Axioms are only propext, Classical.choice and Quot.sound.
The Lean file does not formalize the later norm bounds or unit normalization.

For H=AK−Y/2, Phi(H)=KYH−HYK and R=K³−(Y²K+KY²)/2, compatibility is Phi(H)=R.
Its adjoint is Phi*(W)=YKW−WKY. Full cokernel pairings give the general consistency test.
Exact examples have ranks 12,8,0; a nonsemisimple example can also have rank 12. Discriminant
alone is not a full classifier. T=YK is selfadjoint for skew form K, not the claimed K⁻¹.

For equal q=||K||F²=||Y||F² and symmetric-restriction norm s, hand derivation gives
s²≥1/2+2||H||F²/q. This uses H⊥Y, norm submultiplication and the symmetric test xxᵀ.
A large certified minimum H norm rejects s<1. That target presumes paired skew gain 1;
it does not rule out a counterexample at a larger, different skew gain.

On a rational involution path, t=0 is incompatible despite zero moments. Six sampled
nonzero points are compatible. Minimum-H certificates exclude five; t=1/2 remains
inconclusive with that bound. At t=1/2, minimization over all nine compatible nullspace
directions yields stronger fixed-probe bounds:

- Q: s²≥3483573947231/1848445440000 ≈1.884596576.
- I: s²≥8193163298903/5845607424000 ≈1.401593146.

These are independently replayed rational computational certificates under hand-derived
inequalities, **not Lean-checked norm-exclusion theorems**. All six sampled pairs exclude
s<1 in this test; no continuous-path or global MF13 conclusion follows.

## Independent critique and failure cases

Seven exact compatibility cases distinguish generic success/failure, degeneracy and non-block
coordinates. Consumers reconstruct binding, rank, full nullspace span, primal equations,
dual/stationarity identities and bounds without producer imports. Six minimum-H and 13 tester
certificates pass; 27 deliberate corruptions are rejected. Coordinate rank-one testers each
have universal minimum zero at t=1/2: a failing particular A does not condemn all A.

The original residual-rejecting implementation is preserved. Failed Lean elaboration attempts
are retained; only the final passing source is accepted. Primary-source screening, failed
access attempts and additional unpromoted probes are disclosed in the role notes.

## Next action and grade

After breadth coverage, spend one 30-minute block comparing exact compatibility and fixed-tester
gates against the existing residual-plus-optimizer path on held-out rational pairs. Measure
useful rejection and checking cost. Formalize the norm-bound bridge before proof promotion.

An additional hand-reviewed lead symmetrizes B=(A+QAᵀQ)/2 while preserving the involutive
coupled pair and not increasing s. This reduces the restricted search to B=QC, C symmetric.
Signature 2/4 and 3/3 cases remain interesting; a qualified tridiagonal argument handles the
single-exception-sign signatures. Additional finite probes support a Frobenius-bound conjecture,
but neither that conjecture nor general family exclusion is proved.

**Quality: 90/100 (18/20)**: faithfulness 4, reproducibility 3, discriminatory value 4,
independent critique 4, actionability 3. High confidence in the concrete Lean obstruction and
rational identities; general usefulness and novelty remain unestablished.

Replay from repository root:

```sh
uv run python work/pod/crossover-60-20261018/cards/M05/domain_exact.py
uv run python -O work/pod/crossover-60-20261018/cards/M05/critic_verify_minnorm.py
uv run python -O work/pod/crossover-60-20261018/cards/M05/critic_verify_testers.py
```

Compile from `lean/`:
`lake env lean ../work/pod/crossover-60-20261018/cards/M05/RepeatedSpectrum.lean`.
