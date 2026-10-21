# M01 domain note: exact elliptic quotient, with the lifting obligations retained

AI-written domain research; inherited root model, exact identifier unavailable. Isolated
campaign artifacts only; original 885 work, searches, certificates and challenges untouched.

## Frozen question and current sources

Can the saved rational 6 by 4 square-sum grid acquire a fifth distinct column, producing
five distinct positive integers with five common factor differences? Read
`work/pod/885/FINDINGS.md`, `work/pod/README.md`, `work/pod/885/extend_6x4.py`,
`work/pod/885/lean/Grid6x4.lean`, the C++ extension code and coverage log, and
`work/pod/885/curves/NOTES.md`. The roster's README is the parent `work/pod/README.md`,
not an absent README inside 885. No old search was launched.

Current sources report no extension through denominator 10^6 for both classes, a stronger
bounded report than the frozen inventory. This remains a reported computation, not a global
impossibility. During this session the independent critic identified uint128 overflow in
C++ candidate squaring inside that range. Accordingly the source-reported range is not
accepted here as independently verified exhaustive exclusion. Parent and critic own that
audit. The Python extension script uses arbitrary-precision integers. Historical novelty
notes contradict one another; this note makes no novelty or priority claim.

The exact normalized grids use rows {0,4N1,...,4N5} and columns {d1²,...,d4²}:

- Class 1: N = [206222625,677376000,2019635200,4786481700,16670745700];
  d = [13440,75936,129360,279840].
- Class 2: N = [10046592,24561225,115706752,281637972,564578560];
  d = [5976,10104,24216,69624].

A rational extra column is w², with w rational, w² distinct from all dj² and
w²+4Ni square for every i. Sign does not distinguish columns. w=0 would require every
Ni square; neither class passes even its first Ni. For w=p/q in reduced positive form,
all 4Ni q²+p² must be integer squares. Their parity matches p, so b=(s-p)/2 is integral,
and b(b+p)=Ni q². Thus a valid extension gives the scaled five integers Ni q² and five
integer differences q*d1,...,q*d4,p. Positivity and distinctness are preserved. Clearing
denominators is essential; a raw nonintegral w is not an integer difference for the old Ns.

## Crossovers and their preserved structure

1. **Arithmetic geometry / quotient-first constraint solving.** Keep three square factors
   on an elliptic curve, then lift through the remaining constraints. This converts part
   of the search to a group law while preserving explicit residual obligations. Breaks
   if an elliptic point is advertised as a full grid without checking all remaining rows.
2. **Constraint-programming propagation.** Use exact square-class or modular restrictions
   from each remaining row as cheap rejection certificates before expensive height search.
   Known columns are positive controls. A local survivor is not a rational point, and
   global non-extension cannot follow merely from finitely many residue tests with survivors.
3. **Formal-methods arithmetic audit.** Treat fixed-width overflow as a different problem
   from mathematical search completeness. A bounded negative needs the enumerator, bounds,
   arithmetic semantics and exclusions checked together. A high-speed zero-hit log alone
   does not certify absence. This transfer became concrete in the critic's overflow finding.

## Elliptic quotient and explicit exact lifting

Put a=4N1, b=4N2 and E: y²=x(x+a)(x+b). Every full extension gives x=w² and
three rational square factors x, x+a, x+b; it therefore maps to a rational E point.
The familiar full-2-torsion descent condition identifies these square factors with points
in 2E(Q), subject to the usual finite/nonexceptional interpretation. We do not need to
trust that theorem merely to generate testable candidates: the explicit identity suffices.
For any rational E point (x,y) with y!=0, define

    w  = (x²-ab)/(2y)
    r1 = (x²+2ax+ab)/(2y)
    r2 = (x²+2bx+ab)/(2y).

Then r1²=w²+a and r2²=w²+b. Algebraically the first difference of numerators is
4a*x*(x+a)*(x+b)=4a*y², and similarly for b. w² is the x-coordinate of the doubled
point. The remaining equations w²+4N3, w²+4N4 and w²+4N5 being rational squares
are independent lifting obligations. This route is already related to the old curves
lane's method; the present contribution is a small explicit certificate and discriminating
probe, not a new general algorithm or a complete Mordell-Weil computation.

## Exact test and result

`domain_quotient.py` uses only Python Fraction and integer square roots. Independently
checks 48 grid entries and 40 positive integer factor-pair witnesses across the two
classes, plus distinctness of all five Ns and four ds. Complete roots and witnesses are
in `domain_quotient_results.json`.

For each class, the four known columns give quotient points Pi. A predetermined seed
list is the four Pi and the twelve Pi+Pj / Pi-Pj for i<j. Double each seed: 16 distinct
finite x-coordinates per class, none equal to a known column. Independently check both
elliptic curve identities and the displayed rational lifting formula. All 32 candidates
pass the first two nonzero-row square tests, and every candidate fails each of the last
three rows. No new column. Each rejection has an exact reduced-fraction numerator or
denominator with floor-root s satisfying s²<n<(s+1)². These are exact arithmetic witness
checks, not Lean-checked certificates of the 32 rejections.

Some denominators greatly exceed 10^6: class 1 range 604 through
2642752881795005157427483; class 2 range 6457649 through
1673203957340740337360690534384. This does not mean the intervening denominators were
searched. The test is exactly 32 specified candidates. It demonstrates why replacing all
constraints by one elliptic quotient is unsound, and why a random small combination route
needs a better selection mechanism before a larger budget.

`domain_doubling.lean` formalizes the two rational lifting identities under precisely
`y != 0` and `y²=x(x+a)(x+b)`. It does not prove a full extension, the group-law theorem,
a complete point enumeration, or global non-extension. Compile status and axiom audit are
recorded in `domain_doubling_compile.log`; initial failed imports are retained separately.
Final successful status is reported to PM separately before promotion.

## Primary-source checks and modest scope

[Bekker and Zarhin, The divisibility by 2 of rational points on elliptic curves](https://arxiv.org/abs/1702.02255)
reproves the known rational-2-torsion divisibility criterion; it is established background.
[Halbeisen and Hungerbühler, Halving formulae for points on elliptic curves](https://people.math.ethz.ch/~halorenz/publications/pdf/div2.pdf)
gives explicit halving formulae and the rational square-factor criterion. These support
using the quotient, not claiming its residual lifting constraints disappear.
[Choudhry, Two sets of integers such that all elements of the sumset of the two sets are perfect squares](https://arxiv.org/abs/2508.07806)
provides parametric (3,3), (5,3), and (4,4) constructions. We checked metadata/abstract
for the latter and the halving paper's primary PDF; no exhaustive current literature audit
or novelty assessment was performed here.

## Domain recommendation

GO for certified quotient-and-lift machinery or a targeted square-class sieve; NO-GO for
interpreting arbitrary elliptic quotient points or bounded zero-hit logs as the answer.
A useful next test is to attach exact residual square-class exclusions to a finite,
predeclared set of quotient combinations, preserving known columns as positive controls.
Before relying on q<=10^6 exclusion, repair or independently certify arithmetic bounds in
an isolated copy and reproduce the affected range; coordinate with original 885 owners.
Any complete non-extension claim needs a global rational-point argument, not more height.

Quality estimate: faithfulness4, reproducibility4, discrimination3, critique4, actionability3
=18/20 (90%). Confidence high in exact finite arithmetic, low that these small group-law
combinations alone reveal a new column. PM owns the final gate and continuation allocation.

## Independent review update

The critic independently reproduced the two grids, all 32 distinct positive quotient
candidates and all 96 nonsquare-floor certificates using a separate checker that imports
no producer code. The critic also supplied positive-x, nonzero-y elliptic points obtained
by adding the 2-torsion point (0,0) that fail the x-square lift, strengthening the negative
control against treating a generic quotient point as a column.

After finding the overflow, the critic derived a separate 12-branch exact gap certificate
excluding all potentially overflowing *column* candidates through q<=10^6. That can salvage
the arithmetic exclusion for this range when composed with the original enumeration;
row-search arithmetic and complete log/enumerator auditing are separate obligations. The
initial concern above records the route to the fix, not an assertion that the certificate
has failed. Parent determines whether the combined bounded result meets acceptance.

## Resumed initial-session derivation

See `domain_gap.md` for an additional, different transfer: exact asymptotic branch-and-bound.
For a common difference p between A<B at denominator q, derived
`p³ < AB(B-A)q⁴/gcd(A,B)` and a floor-aware fixed-factor exclusion valid for all q.
Reduced fractions also partition the base factor into 32 /16 square classes for the two
saved bases. These prune infinite families but leave unbounded denominators and do not
prove non-extension. Three algebraic gap lemmas compile; the integer floor/gcd bridge
and cubic consequence are hand-derived, not mislabelled as formalized.
