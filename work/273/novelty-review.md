# Novelty review: smooth prime-minus-one covering exclusions

Reviewed October 18–19, 2026. AI disclosure: written by the OpenAI Codex program manager
subagent requested by Mike. This is a scoped literature review, not a priority certificate.

## Conclusion at this checkpoint

The specific exclusion of every finite distinct covering with moduli `m≥4`, `m+1` prime, and
all prime factors of `m` at most 7 was **not located in the inspected sources**. The analogous
eleven-smooth exclusion was not located either. That is not proof that either result is novel.
The full seven-smooth theorem now passes Lean kernel compilation, with only `propext`,
`Classical.choice`, and `Quot.sound`; the PM independently passed its source-level faithfulness
audit. Eleven-smooth presently has exact Python evidence only. This proves a restricted-family
theorem, not the full problem 273. The integrated-project build also passed, with 8,972 jobs.
The final checkpoint, including the later timing-contract module, passed with 8,973 jobs.

The broad method is not new: optimized partial coverage plus a reciprocal bound for the
remainder appears explicitly in prior covering-system work. CRT-compatible fibers, finite
union bounds, and geometric-series tails are also established tools. A defensible contribution,
subject to further priority review, is the **specific infinite-family restriction and its
explicit kernel-checked certificate**, not the invention of overlap-aware covering bounds.

## Exact claim being checked

For any finite set of distinct natural moduli `D`, with `m≥4`, `m+1` prime, and
`m=2^a 3^b 5^c 7^d` for each `m∈D`, and for any selection of one residue class per modulus,
some integer is uncovered. The exponents have no upper bound. The proved period theorem also
gives at least `57/10000` uncovered points per unit length in a shifted interval of any common
period divisible by 60. It does not phrase this as an asymptotic-density theorem.

Excluding seven-smooth moduli implies that any covering for problem 273 must use a modulus
with a prime factor at least 11. The eleven-smooth extension would raise that to 13. Neither
statement resolves problem 273, excludes arbitrary moduli, or asserts a bound on their sizes.

## Directly related sources inspected

**The author's problem-273 research repository.** Its manuscript states a cutoff `p>877`, a
positive reciprocal-budget excess, and several fixed-period exclusions. Its smooth subpool
discussion and scripts do not state the proposed seven- or eleven-smooth infinite-family
exclusion. A finite period excludes bounded exponents, which is a different quantifier. The
manuscript's parity comment does not justify forcing one half to omit both small moduli: they
can belong to different halves. Our argument does not use it. The review does not treat the
author's claims as independently verified merely because they are written in theorem form.
[Manuscript](https://raw.githubusercontent.com/idealombrer/erdos-273-covering-pm1/master/PAPER_273.tex),
[repository](https://github.com/idealombrer/erdos-273-covering-pm1).

**Harrington, Klein, Lowrance, and Trifonov, 2026.** Theorems 1.3 and 1.5–1.12 describe many
coverings with restricted prime factors. In particular, five-smooth distinct coverings exist
with minimum modulus 8, while their general upper bound is 9. Those results do not forbid our
minimum-modulus-4 sparse pool. Theorem 1.9 bounds coverage by reciprocal sums and corrections
from coprime pairs/triples, under a three-prime-factor condition. Our original moduli are all
even, so these coprime corrections vanish; the seven-smooth family also has four prime factors.
Using the theorem on parity subcovers would require a separate argument about their disjoint
modulus allocations. No immediate implication was found.
[Full paper, arXiv:2605.18644v1](https://arxiv.org/html/2605.18644v1).

**Minimum modulus 7 / least common multiple 10080, 2026.** Section 6 explicitly partitions
moduli into a selected subset and a remainder, optimizes actual coverage of the subset, then
adds the remainder's reciprocal sum. This is direct prior art for the broad partial-coverage
strategy. Its stated result concerns a minimum modulus and bounded least common multiples,
not prime-minus-one smooth families with arbitrary exponents. Our conditional gcd capacities
retain information about the uncovered set, but this review has not established that this
refinement is itself new.
[Full paper, arXiv:2607.19029v1](https://arxiv.org/html/2607.19029v1).

**Filaseta and Kalogirou, 2024.** Their main result forces reciprocal mass strictly above one
when the minimum modulus exceeds four, with an extension based on the uncovered three-smooth
part. This does not exclude a pool of reciprocal mass around 1.067. More subtly, the
multiplicative density recursion in Section 3, equations (13)–(15), is derived under an explicit
assumption that the relevant small-modulus classes do not overlap. That assumption is part of
their contradiction proving excess budget. Dropping it would incorrectly turn their argument
into a blanket smooth-family exclusion. It is not available for our arbitrary residue choices.
[Full paper, arXiv:2407.15280v1](https://arxiv.org/html/2407.15280v1).

**Hough and Nielsen, restricted divisibility.** Their Theorem 1 requires a modulus divisible by
2 or 3 in every distinct covering. Our moduli are already even, so that conclusion is automatic
and does not exclude the family. Their development also uses uncovered-set fibers, emphasizing
that retaining conditional information is established methodology.
[Primary paper, arXiv:1703.02133](https://arxiv.org/pdf/1703.02133).

**Balister, Bollobás, Morris, Sahasrabudhe, and Tiba.** Theorem 1.4 gives the necessary condition
`2|Q` or `9|Q` or `15|Q` for the overall least common multiple `Q`; again `2|Q` is automatic here.
Theorem 1.1's density bound requires sufficiently large minimum modulus, and Theorem 8.1's
explicit noncoverage threshold is 616000. Our family permits modulus 4. Their general distortion
sieve could potentially certify our family after additional arithmetic and tail estimates;
that is a possible alternative proof, not a stated corollary already identified in this review.
[Primary paper, arXiv:1811.03547](https://arxiv.org/pdf/1811.03547).

## Search coverage and limitations

Queries included distinct covering systems with largest prime factor restrictions, five-/seven-/
eleven-smooth moduli, prime-minus-one coverings, and problem 273 with smoothness. The review
followed primary arXiv papers and the problem-specific author's manuscript rather than relying
on search summaries. Some direct erdosproblems.com requests were blocked; an earlier root-agent
forum review supplied bounded-search context. No absence claim is based on those access failures.

The inspected statements do not make the proposed result a trivial corollary. This is a limited
comparison, not a proof that no combination of earlier lemmas implies it. Unindexed notes,
theses, revised versions, or unpublished specialist knowledge may contain the same result.
No outreach or submission occurred.

## Required statement audit before reporting success

The final theorem must quantify over an arbitrary finite family and arbitrary residue choices,
require distinct moduli, require primality of `m+1`, and admit arbitrary smooth exponents.
It must conclude an uncovered integer or a positive density, not assume the mass/fiber bounds
as unproved hypotheses. Translation normalization must cover all choices; adding missing
prefix classes must not narrow the family. The tuple representation must not lose any valid
modulus or violate distinctness. The common period must be positive and divisible by all
selected moduli. Only then can the component certificates support the advertised theorem.

Current audit status: the PM inspected the complete proof in
`lean/Research/CoveringFamily.lean`, including `seven_smooth_period_gap` and
`seven_smooth_not_cover`. The statements have arbitrary finite distinct moduli, arbitrary
integer residues, primality, `m≥4`, and unbounded smooth exponents, with no hidden capacity
hypothesis. Evenness is derived; chosen representations recover their moduli; absent prefix
classes only shrink the survivor set; translation handles negative residues. The existence
wrapper constructs a positive common period. The stronger theorem explicitly counts at least
`57/10000` uncovered points per unit length in the shifted common-period interval beginning
at `r 4`; it does not phrase this as asymptotic density. Source-level faithfulness passes;
the root subsequently verified direct compilation of the complete module with exit code zero.
Both final theorems print only `propext`, `Classical.choice`, and `Quot.sound`. This closes
the full restricted-family proof gate; the separate integrated-project build subsequently
passed with 8,972 jobs.

Approved challenge files remain untouched; no human approval, full problem solution, or
mathematical priority is claimed.
