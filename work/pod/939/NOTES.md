# Lane 939 — algebraic-number-theory notes (r = 5, with a side glance at r = 4)

AI-written working notes (2026-10-18/19). Every claimed hit is re-checked with `verify.py`
(exact integers, sympy.factorint). Negative results are recorded too.

Problem (FC `Erdos939.erdos_939`): `Finset.Coprime S` is `S.gcd id = 1` (setwise gcd, confirmed in
`FormalConjecturesForMathlib/Data/Nat/Prime/Finset.lean`). r = 5: find 3 distinct positive 5-full
A, B, C with gcd(A,B,C) = 1 and A+B+C 5-full. Known: Cambie, Kitamura (both re-verified, `verify.py`).

## 0. Summary of outcomes

| item | result |
| --- | --- |
| exhaustive MITM over *all* 5-full numbers, D ≤ 1e16 (no coprimality pruning) | only the 2 known solutions → closes Cambie's open case "all pairwise gcds > 1" |
| same, D ≤ 1e17, 1e18, **1e20** | only the 2 known solutions |
| same, D ≤ 1e22 | running (`runs/mitm5_1e22.*`) |
| r = 4: a+b=c, 4-full, coprime, c ≤ 1e14 (Cambie's bound reproduced) | 0 solutions, < 1 s |
| r = 4: c ≤ **1e18** | 0 solutions (246,653 4-full numbers) |
| r = 4: c ≤ 1e20 | queued |
| "Cohn surfaces" A X^5+B Y^5+C Z^5 = D W^5 for the two known (A,B,C,D), all \|coords\| ≤ 4000 | no point other than (1,1,1,1) (not even 2+2 or degenerate ones); H = 40000 running |
| polynomial / rational-curve families | all natural constructions blocked (§3); problem is an *orbifold of general type*; a family would be an "unexpected" curve |
| genus-1 curves: twisted Fermat quintics with a rational line | exactly two 2-nodal genus-1 plane quartics per surface (μ^5 = −c/4, −4c), rational for c ∈ {4,8}·m^5, but they live on planes with μ < 0 ⇒ **positivity obstruction**, no valid solutions (§3.3) |
| genus-1 orbifold curves of degree 5 | complete classification: over Q none; over Q(√5) exactly the golden-ratio curve E_φ with the new identity φ³ − φ² s_P + φ s_{2P} + s_{3P} = 0 (§3.4) |
| calibrated heuristic | ≈ 0.05–0.1 expected coprime solutions per decade of D; ≈ 1.2 expected below 1e18 (observed 2); tail beyond 1e18 ≈ 0.2–0.4 (§4) |

No new solution. No family. The evidence (search + heuristics + geometry) points towards *finitely many*
for r = 5, with any family requiring a genuinely exceptional curve on a general-type orbifold surface.

## 1. Tools (all in this directory)

* `verify.py` — exact verifier (`uv run --with sympy python verify.py [r A B C ...]`).
* `mitm5.c` — meet-in-the-middle A+B = D−C over all 5-full numbers ≤ N, 128-bit, residue buckets
  (use a *prime* modulus: 5-full numbers are wildly non-uniform mod 2^k, bucket 0 mod 4096 held 7 % of
  all pairs), pthreads. Reports SOL (gcd 1), counts DUP (C ∈ {A,B}) and NONCOP (gcd > 1).
  1e16: 21 s; 1e17: 159 s; 1e20 (n = 122,594 five-full numbers): ≈ 40 min on 4 loaded cores.
* `full4.c` — r = 4 search a+b=c with hash-set membership and a residue prefilter mod 2^4·3^4·5^4.
* `surf5.c` — integer points on a X^5 + b Y^5 + c Z^5 = d W^5 (signed coords, MITM, classifies the sign
  pattern: VALID3+1 / TWO+TWO / ZERO).
* `quartic_pencil.py`, `hyperosc.py` — the sympy computations of §3.3, §3.4 (logs in `runs/`).
* `heuristic5.c` — Monte-Carlo expectation per decade (§4).
* `queue.sh` — sequential job queue (≤ 4 cores). Logs: `runs/queue.log`.

Known solutions in "weighted Fermat" form:
Kitamura 17·34^5 + 7·49^5 + 1029·42^5 = 1521·39^5 (i.e. 2^5·17^6 + 7^11 + 2^5·3^6·7^8 = 3^7·13^7),
Cambie 200·90^5 + 92·92^5 + 143^5 = 9·183^5 (i.e. 2^8·3^10·5^7 + 2^12·23^6 + 11^5·13^5 = 3^7·61^5).
Both are *not* pairwise coprime (Kitamura: 2 | A,C; 7 | B,C; 3 | C,D. Cambie: 2 | A,B; 3 | A,D).

## 2. Exhaustive searches (negative results)

* `mitm5` has **no pruning by coprimality**, so Cambie's remaining case (gcd(a,b), gcd(b,c), gcd(a,c) > 1,
  gcd(a,b,c) = 1, d < 1e16) is now excluded: for D ≤ 1e20 the only primitive solutions are the two known
  ones (each found 3× as expected, one per choice of C). Counts at 1e20: NONCOP ≈ 8.7e7 imprimitive
  quadruples, DUP ≈ 1e6 with a repeated summand, SOL = 6 = 2 × 3.
  Note: 1 counts as 5-full (vacuous) and is included; no solution uses it.
* Imprimitive quadruples are ~10^7 times more numerous than primitive ones: allowing one prime (say 2)
  to appear with arbitrary exponent changes the counting regime completely. The primitive problem is
  "locally hard" at small primes.
* r = 4: no coprime a+b=c with c ≤ 1e18 (so max(a,b) > 1e18 − min, improving Cambie's 1e14).

## 3. Why there is no cheap family for r = 5 (the geometry)

### 3.1 Orbifold reformulation and the dimension count
A solution is a rational point (A:B:C) of the plane {A+B+C−D=0} ≅ P^2 whose intersection
multiplicities with the four lines A=0, B=0, C=0, D=0 are, at every prime, 0 or ≥ 5. In Campana's
language these are **integral points of the orbifold (P^2, Δ), Δ = (4/5)(L_1+L_2+L_3+L_4)**, four
lines in general position (a projectively unique configuration with symmetry group S_4).
K_{P^2} + Δ = (−3 + 16/5) H = (1/5) H > 0: the orbifold is of **general type**. For comparison:
r = 3, two summands: (P^1, (2/3)·3 pts), K_orb = 0 (elliptic — Nitaj/Cohn families); r = 4, two
summands: K_orb = 1/4 > 0; r ≥ 6 with r−2 summands: (P^{r−3}, r hyperplanes, weight 1−1/r),
K_orb = (1 − (r−2)/r)... positive too, but the Price/GPT monomial curve passes through the deep
strata where ≥ 3 hyperplanes meet, which is possible only in P^{≥3}; in P^2 four general lines have
no triple points. The heuristic count N^{−K} matches: #solutions with D ≤ N ~ N^{−1/5} (r = 5).
Consequence (Campana/Vojta conjecturally; Brownawell–Masser unconditionally over function fields):
an infinite family must come from an orbifold curve of genus ≤ 1 on (P^2, Δ), i.e. a rational or
elliptic curve meeting each L_i only with multiplicities ≥ 5 (on the normalisation). Expected
dimension of every such configuration is negative; they exist only by symmetry ("miracles").

### 3.2 Polynomial identities (rational orbifold curves), with the X=q^5, Y=B^5 trick
* Terms c_i X^{a_i} Y^{b_i} P_i(X,Y)^5 with two free coprime 5-full numbers X, Y (the Price trick for
  r ≥ 6 is the case P_i ∈ {1, X±Y}). For r = 5 we need 4 terms. Degree in (X,Y) ≤ 8 ⇒ all P_i linear
  ⇒ Waring-rank / Vandermonde arguments show only the degenerate Fermat lines L_1^5+L_2^5 = 0 occur.
  General count: unknowns Σ deg P_i + 2 vs. equations D − 2 with D ≥ 5 max deg P_i ⇒ impossible
  generically beyond the degenerate degree-5 case.
* Merging two binomial terms: (X+Y)^5 − (X−Y)^5 = 2Y·N(Y + i·tan(π/5)X) with
  5X^4+10X^2Y^2+Y^4 = ∏_{k=1..4}(Y + i tan(kπ/5) X) a norm form from Q(ζ_5). Forcing it to be a 5th
  power means Y + τX = ε γ^5 in Z[ζ_5] with (X,Y) in a rank-2 sublattice: the curve {γ ∈ P^3 : εγ^5 ∈ W}
  is a complete intersection of two quintics, genus 76 ⇒ finitely many (Faltings). Same for the other
  two mergers (X^2+2Y^2 and 10X^2+Y^2 are norms from Q(√−2), Q(√−10), but X, Y are then degree-5 forms
  that would also have to be 5-full). Dead.
* Rational curves with all multiplicities ≡ 0 mod 5 lift (unramified) to rational curves on the Fermat
  quintic F_5. Known ones: 75 lines (degenerate identities) and the 125 conics coming from
  (x+y+z)^5 − x^5 − y^5 − z^5 = 5(x+y)(y+z)(z+x)(x²+y²+z²+xy+yz+zx) (the conic {e_1 = e_2 = 0}, on which
  p_5 = 0 by Newton's identities). Over Q a conic/line on a twist a x^5+b y^5+c z^5+d w^5 = 0 is
  Galois-stable only when the twist is trivial, and then the conic is positive definite (no real
  points); its image in the orbifold P^2 is a degree-10 rational curve birational to a pointless conic.
  Dead.

### 3.3 Genus-1 curves on the twisted Fermat quintics (two perfect fifth powers)
Diagonal surfaces a x^5+b y^5+c z^5 = d w^5 contain a rational line iff (after scaling) they are
S_c : x^5 + y^5 = c (w^5 − z^5), c > 0 (A = x^5, B = y^5, C = c z^5, D = c w^5, rad(c) | z, w).
Pencil of planes through L = {x = −y, w = z}: P_μ : x + y = μ(w − z), section = L + residual quartic Q_μ.
Q_μ is singular off L exactly at points whose tangent plane contains L: x_0^4 = y_0^4, z_0^4 = w_0^4.
Exact computation (`quartic_pencil.py`, log `runs/quartic_pencil.log`):
* μ^5 = c: 5 nodes ⇒ Q_μ reducible (for c = 1 it is the 3 lines + conic above);
* μ^5 = −c/4 and μ^5 = −4c: exactly 2 (complex-conjugate) nodes, Q_μ irreducible over Q(i) ⇒
  geometric genus 1. Rational iff c = 4m^5 (μ = −m) or c = 8m^5 (μ = −2m).
  Example c = 4, μ = −1: Q = w^4+w^3y+2w^2y^2−3w^2yz+2w^2z^2+2wy^3−4wy^2z+3wyz^2+y^4−2y^3z+2y^2z^2−yz^3+z^4,
  nodes at (y,z,w) = (1±i, 1, −1); singular locus Gröbner basis [y²+2y+2, z+1].
* **Positivity obstruction:** on P_μ with μ < 0, if x, y > 0 then w < z, contradicting x^5+y^5 > 0; all 16
  sign patterns checked — no pattern makes exactly one of x^5, y^5, c z^5, −c w^5 the odd one out
  while satisfying the plane equation. So these genus-1 curves give at best "2+2" weighted identities
  x^5 + 4 z^5 = y'^5 + 4 w^5, and a search |coords| ≤ 150 found no rational point off L on either curve.
  Planes tangent at ≥ 5 points (needed for genus ≤ 1 without a line) are codimension 5 in a 3-dim
  family — only via symmetry, and those are the μ^5 = c planes. Dead for positive solutions.

### 3.4 Genus-1 orbifold curves of degree 5 — complete classification (new)
Degree-5 orbifold curve of genus 1 ⇒ E → P^2 by a degree-5 bundle H with f^*L_i = 5 p_i, p_i rational,
p_i − p_j ∈ E[5] ⇒ E has a rational 5-torsion point ⇒ Tate normal form
E_d : y² + (1−d)xy − dy = x³ − dx², P = (0,0), and the four sections are the "hyperosculating"
functions s_{bP} ∈ L(5O) (divisor 5(bP) − 5O). Heisenberg/Schrödinger structure: translation by P acts
diagonally on L(5O) with eigenvalues ζ_5^i, the five s_{bP} are (ζ^{ib} a_i)_i, so
rank span{s_{bP}} = #{i : a_i ≠ 0}, and ι: a_i = a_{−i}. Four are dependent ⇔ rank ≤ 3 ⇔ a_1 = 0 or a_2 = 0.
Exact computation (`hyperosc.py`, log `runs/hyperosc.log`):
  s_P = y − x² + xy, s_{2P} = −d³ + (3d²−d³)x + (d²−d)y − 2d x² + xy,
  s_{3P} = d² − (d²+2d)x + (d²−d)y + (d+1)x² + xy, s_{4P} = −d + (1−2d)x + y + (2−d)x² + xy,
  det[s_O s_P s_{2P} s_{3P} s_{4P}] = −(d² − 6d − 1)(d² − d − 1)²,  rank ≤ 3 locus: d² − d − 1 = 0.
So the only such curves are over Q(√5), d = φ = (1+√5)/2 (j(E_φ) = −25/2, not CM), with the identity
    φ³ · 1 − φ² · s_P + φ · s_{2P} + s_{3P} = 0      on E_φ
(verified symbolically; `/tmp/phi_identity.py`). A genus-1 orbifold curve of degree 5 on (P^2, Δ) over
Q(√5) — but **none over Q**, so no degree-5 elliptic family for the integer problem. (d² − 6d − 1 = 0,
i.e. d = 3 ± √10, gives rank 4: a 5-term relation, the r = 6 regime, also irrational.)
Higher degree (10 = 5+5, 11 = 5+6, …): expected dimension ≤ −2; a Heisenberg-level-10 search is possible
but was not run.

### 3.5 Cohn's trick and its r = 5 analogue
Cohn (1998): (3-full)·(cube) is 3-full, so one solution a+b=c gives the elliptic curve aX³+bY³=cZ³
∋ (1,1,1) and hence infinitely many. For r = 5 each known solution gives the quintic surface
A X^5 + B Y^5 + C Z^5 = D W^5 ∋ (1,1,1,1), all of whose integer points are automatically 5-full solutions
(coprimality: a prime p | gcd iff p | Y and (p | C or p | Z), etc. — a congruence condition). The surface is
a twist of F_5 (general type): no group law, and its Q-curves of genus ≤ 1 are twists of those on F_5,
which by §3.2–3.3 are not available. Searched anyway (`surf5.c`): no primitive point with |X|,|Y|,|Z|,|W| ≤
4000 on either surface besides (1,1,1,1), in any sign pattern. (The MITM to 1e20 only covers W ≤ 59.)

## 4. Calibrated heuristic (`heuristic5.c`)
Sample coprime triples from the actual list of 5-full numbers ≤ 1e18, weight by the empirical density of
5-full numbers near D times the empirical relative density of D's residue class mod 2^5, 3^5, 5^5, 7^5, 11^5
among 5-full numbers. Expected coprime solutions per decade of D:
1e10: 0.08, 1e11: 0.10, 1e12: 0.09, 1e13: 0.12, 1e14: 0.08, 1e15: 0.07, 1e16: 0.06, 1e17: 0.05; total ≤ 1e18 ≈ 1.2
(observed 2 at 1.4e11 and 1.8e12). The slow decay (≈ ×0.88 per decade instead of 10^{−1/5}) is due to
the secondary terms in the count of 5-full numbers; the tail beyond 1e18 is ≈ 0.2–0.4 expected solutions,
most of it below 1e25. (Naive "γ^4 N^{−1/5}" with γ_5 ≈ 10 is badly wrong: 79 % of 5-full numbers are
divisible by 32 and 63 % by 243, so the primitive problem is dominated by local conditions.)

## 5. Best next ideas (ranked)
1. Finish the exhaustive MITM to 1e22 (running; ≈ 5 h) and, with a disk-backed bucket pass, to 1e24–1e25
   (n ≈ 2–3·10^5 five-full numbers, ~10^10–10^11 pairs; feasible in a day). This covers most of the
   heuristic tail mass and either finds a third sporadic solution or makes "finitely many" very plausible.
2. Classify curves of genus ≤ 1 on the Fermat quintic surface F_5 beyond lines, conics and the 2-nodal
   quartics (literature: lines/conics on the Fermat quintic *threefold* are classified — Albano–Katz,
   Testa/Heath-Brown — but I found no classification for the surface). Any new genus-≤1 curve with the
   right Galois/positivity structure on a twist a x^5+b y^5+c z^5 = d w^5 would be a family.
3. Degree-10 genus-1 orbifold curves via the level-10 Heisenberg structure on X_1(10) (sections
   (α+βh_t)^5 · s_{−t} ∈ L(10O), 4 of them dependent), exploiting ι-symmetry to lower codimension, as
   the φ-miracle did in degree 5.
4. r = 4: extend `full4` to 1e21–1e22 (cheap); heuristically expected count ~N^{−1/4}, so a hit would be a
   genuine surprise.
