# Literature audit — Erdős 128, cut + independent-set bound

Date: 2026-09-09. Sources were downloaded and read in full, not summarised from
abstracts. This file exists so that the attribution in the paper can be checked
without repeating the work.

## Sources opened

| Source | How obtained | What was read |
|---|---|---|
| Razborov, *More about sparse halves in triangle-free graphs*, arXiv:2104.09406v2 | PDF downloaded, text extracted | Intro statements, **Section 4.5 in full**, Section 5, bibliography |
| Balogh–Clemen–Lidický, *Max cuts in triangle-free graphs*, arXiv:2103.14179 | arXiv HTML | Theorem 2 statement and hypotheses |
| Sarid, `aimir/erdos-128-sparse-halves` | repository README | Method, bound, dependencies |
| erdosproblems.com/128 | web | Status, prior results, claims |

## Finding 1 — the α ≥ 3/8 branch of the envelope is Razborov's, verbatim

Razborov's introduction states:

> "Let α(G) be the normalized (by n) independence number of G, and assume that
> α(G) ≥ 3/8. Then β(G) ≤ (1/2)·α(G)·(1/2 − α(G))."

This is the second branch of `f` in the paper. It is **not** new here and the
paper says so.

## Finding 2 — the extension to α ≥ 1/3 is one line of Case 1, and nothing else

Razborov, Section 4.5, Case 1, immediately after his displayed bound:

> "The right-hand side is a concave quadratic function in p_b, with maximum at
> p_b = 3/4 − α which is ≤ α since we assumed α ≥ 3/8. Hence, since p_b ≥ α we
> can plug in p_b := α and this completes the analysis of Case 1."

For α < 3/8 the substitution p_b := α is unavailable, but 3/4 − α then lies
strictly inside [α, 1/2], so the maximum can be evaluated there instead. That
substitution yields (3/2)α² − (5/4)α + 9/32, the first branch of `f`. **That is
the entire extension.**

Razborov's Case 2 ends:

> "Finally, Q₁ is quadratic concave in p_b and ∂Q₁/∂p_b|_(p_b=α) = (1−3α)/2 < 0
> (as α ≥ 3/8). Since p_b ≥ α, we get Q₁(α,p_b) ≤ Q₁(α,α)."

The condition actually used is (1−3α)/2 ≤ 0, i.e. **α ≥ 1/3**, not α ≥ 3/8.
The same threshold α ≥ 1/3 is what makes his second-moment interval
1/2 − α ≤ e_B(w) ≤ p_b/2 non-degenerate at p_b = α. So Case 2 holds on the
wider range with no modification whatsoever. His polynomial

> Q₁(α, p_b) = (13/16)α² − (9/8)α·p_b − (3/16)p_b² − (1/4)α + (1/2)p_b

is identical, term for term, to the one obtained here. Consequently the earlier
description of this work as "extending the completion calculation to
independence ratio 1/3" **overstated the contribution** and has been corrected
in the paper, README, RESULTS and submission draft.

## Finding 3 — the combination with max-cut appears to be new

Razborov cites Balogh–Clemen–Lidický as `[BCL21]` in his bibliography, but does
not combine it with his Theorem 3.6 anywhere in the paper. His Section 5 asks a
different question:

> "we would like to ask to extend Theorem 3.6 to a neighbourhood of the critical
> value α = 2/5"

— i.e. to prove the full conjecture for α ≥ 2/5 − ε, which is not what is done
here. Sarid's repository combines BCL with a flag-algebra C₄ bound, not with an
independence bound. No source found states the step of Section 3: delete the
edges inside the smaller side of a max-cut so that side becomes independent,
apply the completion bound to the modified graph, and pay the deleted density.
**This is where the contribution lies**, and it is what the paper now claims.

## Finding 4 — citation corrected

The earlier draft cited the max-cut result as "Theorem 1.2(a)". In
arXiv:2103.14179 it is **Theorem 2(a)**, and it is stated *"for n large
enough"*. That hypothesis is now discharged explicitly by the blow-up
proposition rather than passed over in a subordinate clause.

## Residual risk

Novelty was checked against the four sources above and against searches for
newer work. That is not exhaustive: the observation in Finding 2 is small
enough that it may exist unpublished or as folklore, and any bound between
0.02587 and 0.0262 could have appeared since. Before any public claim, a
specialist in extremal graph theory should read Section 2, Case 2 in
particular.
