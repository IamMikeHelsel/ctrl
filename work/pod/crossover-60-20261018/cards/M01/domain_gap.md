# M01 resumed domain work: all-denominator factor-gap pruning

This is a new derivation within the initial session, not a continuation search. It does not
run or change either active 885 search. Model identity inherited/unknown; AI-written.

Let A<B be two of the original positive integers. Any candidate reduced positive w=p/q
has positive integer factors a,c satisfying

    a(a+p)=Aq²,       c(c+p)=Bq².

The polynomial t(t+p) is strictly increasing for t>=0, so a<c. Eliminating p gives

    q²(Ba-Ac)=ac(c-a).

Thus D=Ba-Ac>0, c<(B/A)a, and D is a positive multiple of g=gcd(A,B). Consequently

    g q² <= D q² = ac(c-a)
          < a * (Ba/A) * ((B-A)a/A),

which yields the all-denominator necessary inequalities

    a³ > A²g q²/[B(B-A)],
    p³ < AB(B-A) q⁴/g.

The latter uses p=Aq²/a-a<Aq²/a. All inequalities are strict as displayed, with a,p,q>0.
For fixed q this reduces the asymptotic allowed numerator from the naive O(q²) factor
bound to O(q^(4/3)); equivalently tiny-factor branches a=O(q^(2/3)) below the constant
are excluded. It does not bound q, exclude all branches, or provide a global non-extension.
In normalized t=a/q coordinates the lower bound is only t>C*q^(-1/3), so no fixed
positive interval around t=0 is excluded uniformly in q.

## Stronger floor-aware branch bound

Define L=ceil(Ba/A)-1 and D_L=Ba-A L, where 1<=D_L<=A. Since c is integral, c<=L.
The same eliminated identity and monotonicity give

    q² D_L <= a L(L-a).

Therefore **q²>a L(L-a)/D_L excludes** that entire factor-a branch. Equality cannot be
rejected: (A,B,q,a,p,c)=(2,6,1,1,1,2) is a real common-difference witness exactly on
this boundary. The test is a necessary condition, not sufficient: it only checks one
adjacent integer bracket, and other factor/divisibility/square constraints still apply.

For each actual class, choose the strongest coefficient among larger existing rows:

| Base A | Other B | g | Necessary p³ bound |
|---|---|---|---|
|206222625|677376000|165375|p³ < 397977541714368000000 q⁴|
|24561225|281637972|243|p³ < 7318090134042653265300 q⁴|

Illustrations of the exact floor gate: class1 a=100 is excluded for every q>=1 and
a=1000 for every q>=8; class2 a=100 is excluded for every q>=3 and a=1000 for every
q>=80. These are exact fixed-factor families, not counts of all valid divisors or evidence
that a fifth column cannot exist.

## Denominator-independent square-class partition

Reducedness supplies a separate number-theoretic restriction. Put b=a+p. If a prime ell
outside A divides a, then ell divides q because ab=Aq². Coprimality gcd(p,q)=1 prevents
ell dividing both a and b. Hence its valuation in a equals the even valuation 2v_ell(q).
So the squarefree part d of a divides rad(A), and a=d*r² for one of finitely many d.

- A1=3³*5³*7²*29*43: at most 32 square classes, d|130935.
- A2=3⁵*5²*13*311: at most 16 square classes, d|60645.

This is a genuine finite partition independent of q, but each class retains unbounded r,q.
No rank, complete integral-point argument or global finiteness calculation was performed.
It suggests combining descent branches with the exact gap gate and remaining-row square
classes. Reducedness is essential: A=3,q=2,a=2,b=6,p=4 violates squarefreepart(a)|rad(A)
because p/q was not reduced. Reducing this representation removes the apparent violation.

## Evidence and formal binding

`domain_gap.py` recomputes exact constants and fixed-a cutoffs, checks all known columns
as positive controls, then exercises 20,765 small toy factor candidates with 722 actual
common-difference pairs. It falsely rejects none and records boundary-equality witnesses.
It also tests the reduced square-class implication and its explicit unreduced negative
control. These toy ranges are unrelated to the original large-grid denominator search.
`domain_gap_results.json` records exact data; no floating point is used.

`domain_gap.lean` compiles three lemmas with only propext/Classical.choice/Quot.sound:
(1) eliminated factor identity; (2) bracket necessary inequality; (3) its exclusion
contrapositive. The statement explicitly assumes c<=L and a<=c. It does not pretend to
prove the integer ceil bridge, gcd divisibility, square-class theorem or the all-q cubic
bound in Lean. Those are the elementary derivations above, exact-test corroborated.

Recommendation: GO for a certified branch-and-bound layer before any new search budget.
A useful deliverable would prove the integer floor/gcd bridge and compose it with the
existing enumerator, keeping unbounded denominator coverage explicitly open. This is a
mechanism for faster and safer exhaustive bounded work, not yet a route to global closure.

## Optimize across all row pairs

The cubic p bound does not depend on which row the enumerator used as its base. Computing
all ten A<B pairs in each class leaves class1 unchanged but improves class2 to

    A=10046592, B=24561225, g=243,
    p³ < 14739018868537891200 q⁴.

The earlier class2 constant is the best among partners of its chosen enumeration base;
this new constant is the best among every pair in the saved class. The same inequality
proof applies. Full pair constants are recorded in `global_all_pair_cubic_bounds` in the
JSON. This reduces an upper bound coefficient; it does not count candidate rejections or
establish any new exhaustive denominator range.
