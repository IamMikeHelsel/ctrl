# A cut and independent-set bound for sparse halves

Erdős problem [128](https://www.erdosproblems.com/128) asks whether every
triangle-free graph on *n* vertices has ⌊n/2⌋ vertices spanning at most n²/50
edges. **This repository does not answer it.** It contains a partial bound of

> **β(G) ≤ 2587n²/100000 = 0.02587 n²** for every finite triangle-free graph,
> assuming Balogh–Clemen–Lidický, *Max cuts in triangle-free graphs*,
> Theorem 2(a).

The paper is [`outputs/cut-independent.pdf`](outputs/cut-independent.pdf); it is
five pages.

| bound | | source |
|---|---|---|
| 1/16 = 0.0625 | | random half |
| 1/36 = 0.02778 | | Krivelevich 1995 |
| 27/1024 = 0.026367 | | Razborov 2022, flag algebras |
| 131/5000 = 0.0262 | | Sarid 2026, flag algebras + max-cut |
| **2587/100000 = 0.02587** | | **here**, elementary + max-cut |
| 1/50 = 0.02 | | the conjecture, tight at blow-ups of C₅ and Petersen |

No flag algebra and no semidefinite certificate are used, which is the only
reason this is worth anyone's attention: the whole argument is elementary and
therefore checkable by hand and, in principle, formalizable in full.

## What is new here, and what is not

This matters more than the constant, so it is stated first and in detail. The
supporting quotations are in [`LITERATURE.md`](LITERATURE.md).

**Not new.** The completion envelope for independence ratio α ≥ 3/8 is
Razborov's Theorem 3.6 verbatim. His Case 2 already holds for every α ≥ 1/3
without modification: the condition it actually uses is
∂Q₁/∂p_b = (1−3α)/2 ≤ 0, and he assumes 3/8 only for Case 1. The polynomial
Q₁ obtained here is his, term for term.

**The extension is one line.** For α < 3/8 the substitution p_b := α in his
Case 1 is unavailable, but the maximum of his concave quadratic then lies
interior to [α, 1/2], at p_b = 3/4 − α, and may simply be evaluated there. That
gives the branch (3/2)α² − (5/4)α + 9/32. That is the whole of it.

**What we believe is new** is the combination in Section 3 of the paper, six
lines long: take a bipartition realising D₂(G), delete the edges inside the
smaller side so that it becomes independent, apply the completion bound to the
modified graph, and pay the deleted density; combine with the trivial profile
supported on the larger side. Razborov cites Balogh–Clemen–Lidický but does not
combine it with his Theorem 3.6; Sarid combines the same max-cut theorem with a
flag-algebra C₄ bound instead. We have not found this step in the literature,
but it is small enough that it may be folklore, and establishing that is the
main open question about this note.

## Checking it

```
python outputs/verify-cut-independent.py     # standard library only
python outputs/verify-independent.py         # requires sympy and networkx
python formal/verify.py                      # Lean, see formal/README.md
```

The two verifiers were written independently of one another. Both use exact
rational arithmetic throughout; no floating-point value enters any acceptance
decision. Between them they re-derive every polynomial identity symbolically,
re-check every rational margin in the certificate, re-derive the argument's
supremum from scratch, and brute-force β over classical families, circulants,
randomised triangle-free graphs and all 440 triangle-free labeled graphs of
order ≤ 5. `formal/Scalar.lean` carries 17 Lean 4 theorems covering the scalar
optimisation and the polynomial identities, replayed by Lean's kernel, with no
`sorry` and no added axioms.

None of that establishes universality — the analytic proof does that. It
establishes that the arithmetic is not where an error hides.

## What is not claimed

- Not the conjecture. Not a counterexample. Not priority.
- The bound is conditional on Balogh–Clemen–Lidický Theorem 2(a), assumed as
  published. It is stated there for *n* large enough; Proposition 1.2 of
  the paper discharges that hypothesis by a blow-up argument.
- The graph-theoretic content of Sections 2 and 3 is not formalized.
- **No specialist has read the proof.** Section 2, Case 2 is where an error
  would survive both verifiers, and it is the part worth a reader's scepticism —
  though it is also the part that is Razborov's published argument.

## Ceiling of the method

The supremum over the cut parameter of this bound is 0.0258691…, so 2587/100000
is the route's own optimum rounded up. Substituting a perfect max-cut input
(1/25, the other Erdős conjecture on D₂) would give only ≈ 0.02481.
**1/50 is unreachable this way.** An attempt to make the 1/25 improvement
unconditional is recorded, and failed, in
[`outputs/window-closure-attempt.md`](outputs/window-closure-attempt.md); the
one opening that remains is described at the end of it.

## Layout

| path | |
|---|---|
| `outputs/cut-independent.{tex,pdf}` | the paper |
| `LITERATURE.md` | attribution audit, with quotations |
| `outputs/verify-*.py` | the two independent verifiers |
| `formal/` | Lean 4 certificate and its pinned runtime setup |
| `RESULTS.md`, `LOG.md`, `NEXT.md` | status, full work log, next step |
| `work/` | scratch and dependencies, not tracked; see `work-sarid-fetch.sh` |

## Method

This work was carried out with substantial assistance from AI coding and
reasoning agents, which produced and checked the algebra, the rational
certificates and the Lean development, and performed the literature audit. The
author is responsible for the mathematical content. `LOG.md` is the unedited
record, including the failed directions.

Corrections and objections are welcome as issues, and a message saying the
extension is already known would be as useful as one saying it is not.

## References

- A. A. Razborov, *More about sparse halves in triangle-free graphs*,
  [arXiv:2104.09406](https://arxiv.org/abs/2104.09406). Theorem 3.6, Section 4.5.
- J. Balogh, F. C. Clemen, B. Lidický, *Max cuts in triangle-free graphs*,
  [arXiv:2103.14179](https://arxiv.org/abs/2103.14179). Theorem 2.
- A. Sarid, [aimir/erdos-128-sparse-halves](https://github.com/aimir/erdos-128-sparse-halves), 2026.

Paper and prose CC BY 4.0, code MIT; see [`LICENSE`](LICENSE).
