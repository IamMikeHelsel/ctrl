# Lane 885 / curves (arithmetic geometer) — NOTES

AI-written working notes. Everything here is a candidate until a Lean file checks it; every
grid claimed below has been re-checked by `verify_grid.py` (exact Fractions) and by
`recheck_int.py` (sympy full divisor enumeration of D(N)).

## RESULT 1 (2026-10-18 22:45): a 6x4 grid (NOT new: 6x4/4x6 rectangles were already known —
## erdosproblemaday.com/day/885-factor-difference-k5 (July 2026) lists 71 primitive 4x6; this one is
## Lean-checked in work/pod/885/lean/Grid6x4c.lean)

Found by `combine.py lagrange "u=x,v=1" 1 30000`, parameter x = u/v = -911/588 in the
Lagrange/Guy 4x4 family, two extra rows obtained by the group law (see Method).

Integer form A: **5 numbers sharing 4 common factor differences**
    N = 37766958912000, 68748916723200, 314766258325200, 3333331304226000, 4217775226845264
    d = 7142490, 18218160, 30414640, 100110960
Integer form B: **3 numbers sharing 6 common factor differences**
    N = 70221547596375, 218508790732375, 2492797287180375
    d = 7142490, 14215590, 18055770, 36195030, 115690710, 130085034
(D-intersection computed by full divisor enumeration: exactly these 4 resp. 6 elements.)
Rational grid: `grids/g64_lagrange_m911_588.json`. The same configuration appears transposed
at x = -236/265 (`grids/g46_lagrange_m236_265.json`): the Lagrange family is self-dual.

Primitive integer form (common square factor removed, `dedupe.py`):
    N = 9441739728000, 17187229180800, 78691564581300, 833332826056500, 1054443806711316
    d = 3571245, 9109080, 15207320, 50055480
(5 numbers, 4 common differences; each d in D(N) checked by 4N+d^2 = square with parity.)

## Polynomial structure of the Lagrange family (polyrows.py, closure.py, biclique.py)
- polyrows.py enumerates ALL polynomial rows of degree <= 4 (also <= 6, <= 8 tried) for
  polynomial columns via w-z = c D, w+z = delta/(cD) (D monic divisor of delta).  For Lagrange:
  exactly the 4 known rows + 3 new rows (valid on cols {0,1,3}); dually 3 new cols.  So there is
  NO polynomial 5x4 extension of degree <= 8.
- 7x7 polynomial incidence: rows r0,r2,r3 square against all 7 cols, cols c1,c2,c3 against all
  7 rows (polynomial 7x3 and 3x7 grids); the 15 missing entries are 15 distinct irreducible
  quartics (genus 1, ranks 4-6).
- Closure (rows valid on >=3 current cols, and dually) grows 7, 19, 55, 163 = 1+2*3^k: an infinite
  symmetry (reflection-type) group acts.  Max polynomial bicliques at every level: 7x3, 3x7, 4x4.
  Min #missing (each a genus-1 condition) at levels 1 and 2: 6x4: 2, 5x5: 3, 7x4: 3, 6x5: 4, 6x6: 7.
- grid77.py (15 conditions, H=1e5 + group-law box 3 on each Weierstrass model) and scanlevel.py on
  the 55x55 level (2679 quartics, H=2e4, 31473 x-values): 36 nondegenerate 6x4/4x6 hits, ALL the
  same configuration up to equivalence (dedupe.py) — the symmetry group moves it around.
  No nondegenerate 5x5, 7x4 or 6x5 at these heights.
- Level 3 (163x163 closure, scanlevel.py H=1e4, 6 procs, ~1h): 47 hits (21 6x4, 26 4x6), again
  ALL the same configuration (dedupe.py).  No 5x5/7x4/6x5.  The orbit seems to be the only
  low-height 6x4 in this family.
- Is Lagrange special?  polyrows on Choudhry families (t_polyfam.py, t_slices.py): Thm-3 u- and
  v-slices and Thm-4a/4b q-slices, ~270 slice values p/q with p,q<=12: ZERO extra polynomial
  rows or cols (only the 4 known).  So Lagrange's 7x3/3x7 polynomial richness is not shared by
  the Choudhry families; that richness is exactly what made the 6x4 reachable.
- bigx.py: group-law points (box 4, ~30k per curve, heights >> 1e5) on the 6 level-0 conditions:
  all coincidences between conditions occur at small height; nothing new.
- deep.py on the 6x4 grid: all 4 column-triple and 20 row-triple curves (ranks 4-8, ellrank
  bases, box 2): no 7th row, no 5th column, and no column valid for 5 of the 6 rows (no 5x5 inside).

## Method that worked
1. Fact: for columns v1,v2,v3 the admissible rows are exactly x(2P), P in E(Q),
   E: Y^2=(X+v1)(X+v2)(X+v3) (full 2-torsion 2-descent).  Halving formula:
   x(P) = X + s1 s2 + s1 s3 + s2 s3, y(P) = (s1+s2)(s1+s3)(s2+s3), s_i = sqrt(X+v_i).
2. Take a 1-parameter 4x4 family over Q(x) (Lagrange/Guy; Choudhry Thms 3,4 with other params
   fixed).  For each column triple T, halve the 4 rows on E_T over Q(x), form small
   combinations sum n_i P_i (n in [-1,1]^4), double: a new row X(x) valid for the 3 columns
   of T identically.  The single remaining condition X(x)+v_rest(x) = square has square-free
   part F(x); in the Lagrange family three combinations give deg F = 4 (genus 1, rank 4-5,
   hundreds of points): three 1-parameter families of 5x4 grids over elliptic curves.
   (Same by transposition for new columns.)
3. 6x4 = two such new rows valid at the same x (point on the genus-5 fibre product): found
   by intersecting x-sets from hyperellratpoints(F, 30000).

## Structural observations (relations.py)
- In every known 4x4/5x4 grid, on the triple curves the halved row points satisfy short
  relations P_a +- P_b +- P_c in E[2] ("collinear 3x3 subgrids").  Proved: a 3x3 subgrid is
  collinear on the row curve iff on the column curve, since both say
  prod_j(t+v_j) - prod_a(t-u_a) = (lambda t + mu)^2.
- Choudhry's Thm-4 4x4 has a perfect matching row-triple <-> column-triple of collinear subgrids.
- Experiment (collin.py, curves E_{0,a,b}, |a|<b<60): collinear 3x3 bases did NOT extend to 4x4
  more often (0/58k columns vs 8/1.16M for non-collinear).  So collinearity is a symptom.

## Negative / bookkeeping
- ext.py two-sided numeric box search reproduces Pan's 5x4 from its own column triples in <1s.
- Generic curves E_{0,a,b} with |a|<b<=60, rank>=2: only rare 4x4 (rows {P,Q,P+Q,2P} on
  the curve {0,13,28}, and on {0,-51,53}); no 5x4.
- Pan's repo github.com/zoahdev/erdos885-square-sum returned 404 (not reachable).

## Wave 3 (2026-10-19): why Lagrange is rich, and its 2-parameter deformation
Frame: poly77_lagrange.json (column 3 = 0, so rows are squares a_i^2, a_i quadratic).
Incidence: core 3x3 = rows {0,2,3} x cols {1,2,3}; rows {0,2,3} hit all 7 cols, cols {1,2,3}
hit all 7 rows; Lagrange's 4x4 = core + row 1 + col 0.

**K3 / Mordell-Weil explanation (k3height.py, t_k3.py).**  For 3 quartic columns, E_B:
Y^2 = (X+C1)(X+C2)(X+C3) over Q(x) is an elliptic K3 surface (a2,a4,a6 of degree 4,8,12).  For
B = cols {1,2,3}: 12 fibres of type I2, full 2-torsion.  Every polynomial row is X = x(2P) with P a
section of Shioda height exactly 1 (h = 4 + 2 P.O - sum contr; 2P integral forces h(P) = 1).  Gram
matrix of the 7 halved rows (exact): rank 4, equal to <1> + A3(1/2): row 1 is the isolated <1>;
rows {0,2,3,4,5,6} are the 6 root pairs of A3 scaled by 1/2 (inner products 0, +-1/2).  Exactly 14
norm-1 vectors, so 7 rows, matching the complete enumeration.  Richness = a Mordell-Weil lattice
with many minimal vectors.  Picard number >= 2+12+4 = 18, so these K3s have <= 2 moduli.

**Deformations (deform.py, obstr.py, deform_newton.py, deform2.py).**  Naive count for degree-4
polynomial 4x4 grids: 27 params - 24 conditions - 4 (GL2) = -2.  The exact Zariski tangent space
at Lagrange, modulo GL2, is 2-dim for: the 4x4, the 3x7, the 7x3, and the full 7x7 pattern
(34 entries).  Second-order obstruction (exact, F is quadratic) vanishes identically.
So deforming the 4x4 automatically carries the whole 7x7 pattern along: richness persists.

**Explicit 2-parameter family over Q-bar (tt.py, t_two.py):** keep row 1 (a1 = 6(x^2+13x+16)) and
column 0 fixed, and
    C1 -> C1 + t1 (2x^2+6x+7)^2,   C2 -> C2 + t2 (4x^2+10x+1)^2
(the squares are b_11, b_12 up to scale: a1^2 + C1 = 64 w1^2, a1^2 + C2 = 144 w2^2).  Newton
(150-600 digits) converges quadratically to the full 7x7 pattern at every (t1,t2) tried.
**Rationality obstruction:** for rational (t1,t2) the unlabelled configuration is defined over Q,
but the rows/cols lie in a multi-quadratic extension (Galois swaps rows 0<->4, 2<->5, 3<->6).
On the slice t1 = 0 (sfam.py, t_norm.py, exact rational interpolation in t2) all 7 rows are
rational iff
    t2+144, 21(t2+189), 21 t2+2704, 21(25 t2+3024) are all squares
(each a square at t2=0).  A (Z/2)^4 cover of P^1 branched at 5 points: genus 5, so finitely many
points.  (Partial: the first three give a rank-2 elliptic curve, conductor 5578650; at its 6 small
non-trivial points only row 1 survives, which confirms that the 4th class is needed.)
On the slice t2 = 0 the classes are 5(80-t1), t1+64, 2704-5t1, 5(125-t1).
On the diagonal and t2 = 2 t1 slices (t_slice1.py, t_bil.py) the classes are products of
    l1 = t1+64, l2 = t2+144, l3 = 5(125-t1), l4 = 21(t2+189), l5 = 2704-5t1+21t2,
    D' = 15120 - 189 t1 + 125 t2 - t1 t2   (bilinear; it is the common denominator).
All rows rational  <=>  l1, l2, l3, l4, l5, 105 D' are all squares (6 conditions; l1, l2 come from
row 1: a1^2 + C1 = (64+t1) w1^2, a1^2 + C2 = (144+t2) w2^2).  The 4x4 Lagrange sub-pattern
already needs all 6.  With t1 = 125-5a^2, t2 = 21b^2-189: D' = 105(a^2b^2-81), and the locus is
    189-5a^2 = sq, 21b^2-45 = sq, a^2b^2-81 = sq, 25a^2+441b^2-1890 = sq      (Lagrange: a=5, b=3).
Branch divisor of bidegree (5,5) on P^1 x P^1, so K = (1/2,1/2) is ample: **general type**.  So the
rational rich members are expected to lie on finitely many curves (Bombieri-Lang).
  - ssearch.py (5 conditions; it omitted l1, l2), H=60: 13 hits, all Lagrange or degenerate
    (C1 proportional to C2, or rows collapsing; checked with polyrows: tverify_pts.py).
  - ssearch2.py (all 4 conditions, conics parametrised, k, l of height <= 30): 288 hits, all on the
    degenerate curve ab = +-9 (D' = 0) except Lagrange itself.  H = 200 run: see below.

**Lattice form of the richness / the symmetry.**  On E_B (cols {1,2,3}) with core rows P0, P2, P3
(Gram: <P0,P2> = <P0,P3> = -1/2, <P2,P3> = +1/2) the extra rows are exactly
    row4 = 2(P3 - P2),  row5 = 2(P0 + P3),  row6 = 2(P0 + P2)        (exact Gram solve)
i.e. the 6 root pairs +-P_i +-P_j of A3(1/2), and row 1 is orthogonal.  Each extra row is the
collinear-3x3 completion (P_i +- P_j +- P_k = 0) of two core rows, so the closure tree (1+2*3^k)
is generated by these Vieta/collinear completions on successive triple curves.  Elliptic-curve
translations by other sections add nothing at height 1.  **Richness criterion: three rows whose
halved sections have pairwise height pairing +-1/2 on a K3 triple curve (on both sides).**

**Membership of the other 6x4 classes (member.py vs the Lagrange 7x7 polynomial set, all
affine maps (u,v) -> (cu+s, cv-s), both orientations, all anchor pairs).**  Sanity check: our
6x4 is recovered at x = -911/588 with 6+4 hits.  Smooth-lane class 1 and class 2: 0 hits, so no
4x4 subgrid of either lies in Lagrange's family (or in its 7x7 polynomial extension).
  - ssearch2.py H = 200 (38666 x 44104 conic points, 1.7e9 pairs, 6 procs): **only Lagrange**
    (a,b) = (5,3) off the degenerate curve ab = +-9.  So no other fully rational rich member at
    this height.
**Wave-3 bottom line.**  Lagrange's richness is the A3(1/2)+<1> Mordell-Weil lattice of a
rho >= 18 K3 triple curve.  It deforms in an explicit 2-parameter family over Q-bar (above), which
carries the whole 7x7 pattern.  But rationality costs 6 square conditions, cutting out a
general-type surface whose only small rational point is Lagrange.  No rational 2-parameter rich
family exists inside this deformation (up to the search height).  No 5x5 / 6x5 / 7x4.
Next direction: other components of the rich locus, i.e. 3x3 polynomial cores whose sections pair
to +-1/2 on both triple curves, embedded differently; or K3 members with rho = 19, 20 (curves and
points of M), where extra height-1 sections could give a polynomial 5x4.

## Wave 4 (2026-10-19): other rich cores via Klein four-groups; Picard-jump locus

Structure (why Lagrange's E_B has 6+1 rows).  Each quartic column C = c*l1 l2 l3 l4 has 3 root
pairings; pairing k gives a plane Pi_k = span(P_k, Q_k) of binary quadratics, and a row a lies on
it iff a = (nu Q_k - mu P_k)/2 with mu*nu = c.  In Lagrange's E_B (poly77_lagrange.json, columns
1,2 relative to the zero column) the 3 planes of C1 coincide with the 3 planes of C2: the root sets
of C1 and C2 are orbits of one Klein four-group V in PGL2(Q) (klein.py), fixed-point fields
Q(sqrt 21), Q(sqrt 105), Q(sqrt -5).  Each shared plane carries <= 2 rows (a binary quadratic
equation), giving the 6 rows of A3(1/2); the 7th row (the <1> summand, 6(x^2+13x+16)) lies on a
line Pi_k ∩ Pi_k' and costs one extra condition G_1k(a_L)/c1 = G_2k'(a_L)/c2 with c1/G_1k a
square.

Search (vsearch.py split V; vsearch2.py general V = <x->a/x, x->(x-a)/(x-1)>, columns c_j * prod
over V-orbits, c2 forced by a plane-0 row; generic_rows() for the 7th row).  Calibrated on
Lagrange (t_gencal.py: 2+2+2 plane rows + generic row 6(x^2+13x+16), total 7).  Each candidate
then gets polyrows closure (vcheck.py, complete) and Moebius-invariant fingerprint (vinv.py:
multiset of j-invariants of y^2 = C_i - C_j and y^2 = R_i - R_j).
- Configs with 6 plane rows are plentiful (33 at heights (3,3,4)); complete closure shows 6 rows,
  6 columns on the best row triple, maxhit 3: both sides have the A3(1/2) part, i.e. double
  A3-richness looks generic for V-cores (3 parameters = core moduli).  Only the <1> pair is extra.
- MINROWS=7 run (Ha=8, Hu=6, Hc=8, 6 workers, logs/vs7_*.out; stopped after ~45 min, workers 0
  and 4 completed, others partial): 16 distinct 7-row configurations (a = -3/2, -2/3, 2/5, 3/5),
  all with fixed fields {-6, 10, -15} and ALL with the same fingerprint: one new class, "K1".

K1 (poly77_v1.json; also poly77_klein1.json in grid77 format).  a = -3/2,
C1 = -1/8 (x-3/4)(x+2)(x+9)(x-1/6), C2 = 605/648 (x-6)(x+1/4)(x-3/2)(x+1), C3 = 0.
- Polynomial closure 7x7, 37/49 incidences (Lagrange: 34/49); column hits [4,4,4,4,7,7,7], row
  hits [5,5,5,5,5,5,7] (Lagrange: [3,3,3,4,7,7,7] both, self-dual; K1 is not).  Four polynomial
  4x4 subgrids (each new column + the 3 core columns).  No polynomial 5x4/4x5 (maxhit 4).
- k3height (t_k3v1.py): E_B has 12 I2 fibres; Gram of the 7 halved rows = A3(1/2) + <1>, rank 4,
  pairings in {0, +-1/2}.  Dual (t_k3dual.py): row triple (0,2,4) carries 7 columns (complete
  polyrows), same lattice A3(1/2) + <1>.  So the +-1/2 criterion holds on both sides.
- NOT equivalent to Lagrange: j-fingerprints disjoint apart from 1728 (invariant under Moebius
  in x over Qbar, scaling, and row/column shifts).  Open: whether K1 is a special point (3 extra
  incidences) of Lagrange's Qbar deformation M or lies on another component.  It is not one of the
  ssearch rational points because that frame fixes a1 and the shift quadratics over Q.
- Exact re-check without PARI: recheck_poly_k1.py (sympy sqf_list) -> 37 square incidences,
  biclique rows (0,2,4,6) x cols (0,1,2,3), x=3 gives the rational 4x4
  U = [609961/1024, 1418481/25600, 1089/16, 14641/256], V = [0, -765/16, -7865/144, -9190071/409600].
- grid77.py klein1 (H=1e5 hyperellratpoints + group-law box 3; all 10 entry curves rank 5;
  logs/grid77_klein1_*.log): ~4e4 x values, 190 rational 4x4 and two rational 5x4 (x = -51/8,
  x = 4/17; known shapes).  No 5x5, 6x4, 6x5, 7x4.

Direction 2 (Picard-jump locus, vdeg.py).  V-semi-invariant quartics form a pencil whose degenerate
members are q_k^2 (q = x^2-a, x^2-2x+a, x^2-2ax+a).  C1 - C2 = lam q_k^2 merges two I2 pairs into
I4 fibres (codim 1, fixes c2/c1).  Scan heights (5,4,6) partial plus (3,3,4): 672 + 24 configs with
>= 4 plane rows; complete polyrows (vcheck) gives exactly the predicted 4 rows in every case,
maxhit 3.  No extra height-1 sections on this locus (and plane rows drop from 6 to 4 there).
