# Conditional capacity for prime-minus-one coverings

AI-assisted research note, 2026-10-18 local. **Complete restricted-family Lean theorem checked; no priority claim.** The full Erdős273 problem remains open in
this work. See the program manager report for current verification status.

The proposed seven-smooth result is stronger than a finite search cutoff: any finite family
of congruence classes with distinct moduli m≥4, m+1 prime, and all prime factors of m among
2,3,5,7 leaves an uncovered set of density at least57/10000. An exact Python extension
suggests that allowing11 still cannot produce a covering, with a smaller certified-by-Python
margin. The eleven-smooth calculation has not received the same independent or Lean audit.

## Why the idea can work

A congruence class has density1/m. Counting those densities independently permits the same
integer to pay several coverage obligations. Conditional counting remembers which cells
have already been covered. The small prefix carries this geometric information; an exact
tail bound accounts for every larger modulus, however large its exponents.

An unconditioned weighting cannot repair the issue: for weights of totalW on a period, the
largest class weight for modulusm is at leastW/m by averaging. Its resulting sum-of-maxima
bound is therefore no better than density. Conditioning breaks that symmetry.

## Written argument for the seven-smooth candidate

Given any finite proposed family, add missing prefix moduli4,6,10,12 with arbitrary residues.
They are all admissible, and adding classes can only reduce the uncovered set. Translate
the integers to normalize the residue modulo4 to0. Let the other residues bea,b,c, and put

R = {x in0,…,59 : x mod4≠0, x mod6≠a, x mod10≠b, x mod12≠c}.

For a divisor g of60, let C_g(R) be the largest number of elements ofR in a single
residue class modulog. For another modulusm, g=gcd(m,60), the intersection of one
class modulom with the periodic lift ofR has density at most

    g C_g(R) / (60m).

To see this, use any common periodH of60 andm. For each compatible residue inR there is at
most one simultaneous residue modulo lcm(60,m), and H/lcm(60,m) copies inH. Summing
over compatible residues and using gcd×lcm=60m gives the displayed bound. The Lean
`conditional_class_card_le` lemma proves the corresponding integer counting inequality.

Write a seven-smooth even modulus as2^u3^v5^w7^z, withu≥1 andv,w,z≥0. Retain the exponent
boxu≤10,v≤6,w≤4,z≤3. Within the box, dropm<4 and everym whose successor has a proper
divisor among the primes3 through97. This can only overinclude admissible moduli. There
are616 retained moduli, including the four prefix moduli. After removing the prefix,
the group reciprocal masses are bounded as follows:

| gcd(m,60) | Upper bound for sum1/m |
| --- | --- |
| 4 | 120/1000 |
| 6 | 101/1000 |
| 10 | 21/1000 |
| 12 | 85/1000 |
| 20 | 47/1000 |
| 30 | 56/1000 |
| 60 | 40/1000 |

There is no retained gcd2 group. All moduli in the box divide160030080000, so the
finite sums can be verified with integer arithmetic without rounding division downward.
The Lean `CoveringMass` module checks the sieve implication, division exactness, group
completeness, and these seven bounds.

Outside the box, discard primality and bound all even seven-smooth reciprocal weights.
The full geometric product is35/16. Subtracting the box gives

    35/16 − (1023/1024)(1093/729)(781/625)(400/343)
      = 632647/133358400 < 5/1000.

This bounds every finite set of exponent tuples outside the box, not merely a finite
sample. The Lean `finite_tail_bound` proves that assertion for arbitrary finite sets.

For every one of the720 normalized prefix choices, exact enumeration gives

    1000|R| − [300 + 480C_4 + 606C_6 + 210C_10 + 1020C_12
                        + 940C_20 + 1680C_30 + 2400C_60] ≥ 342.

The same minimum holds withC_20,C_30,C_60 replaced by their universal upper bounds3,2,1;
the bracket then starts with constant8880 and retains only the first four variable terms.
The worst normalized prefix residues include(0,1,1,3). Dividing by60000 gives the claimed
uncovered-density margin57/10000. Strictness is essential when bounding total class mass:
each modulus may contribute only once. This argument does not apply to repeated moduli.

## Formal verification and remaining acceptance boundaries

`Research.CoveringFamily.seven_smooth_period_gap` proves the uniform bound for every
finite set of natural moduli, every integer residue function, and every common period H
with 60 dividing H. Its conclusion counts uncovered points in [r(4), r(4)+H).
`seven_smooth_not_cover` constructs a positive such period and concludes an uncovered
integer. All smooth exponents are unrestricted. Positive two-exponent representation,
translation, missing prefix classes, injectivity, finite sums, tail and CRT bounds are
proved in the dependency chain; no unproved capacity assumptions remain.

Direct compilation and the integrated 8,972-job build passed. Both final declarations
print only `propext`, `Classical.choice`, and `Quot.sound`. The requested program manager
independently audited the statement and proof structure for faithfulness.

This is a restriction on hypothetical coverings, not a solution of Erdős273. It is not
an approved Challenge/Solution binding. Novelty is unestablished: the broad method has
prior art, and the specific restriction was not located in the scoped review. See
`novelty-review.md`. Eleven-smooth still has Python evidence only. No submission,
publication, outreach, or human approval occurred.

Reproduce from the repository root:

```sh
cd lean
lake env lean Research/CoveringFamily.lean
lake build
```
