"""Independent all-denominator inequality and reduced-squareclass checks."""

import json
from fractions import Fraction as F
from math import gcd, isqrt
from pathlib import Path

P = Path(__file__).parent
report = json.loads((P / "domain_gap_results.json").read_text())
for group in report["global_all_pair_cubic_bounds"]:
    assert len(group["pairs"]) == 10
    for pair in group["pairs"]:
        aa, bb = pair["A"], pair["B"]
        assert aa < bb and pair["gcd"] == gcd(aa, bb)
        assert pair["p_cubed_coefficient"] == F(aa * bb * (bb - aa), gcd(aa, bb))
    assert group["best"] == min(group["pairs"], key=lambda item: item["p_cubed_coefficient"])
for record in report["classes"]:
    A = record["A"]
    for row in record["all_pair_bounds"]:
        B = row["B"]
        g = gcd(A, B)
        assert row["gcd"] == g
        assert F(row["a_cubed_coefficient"]) == F(A * A * g, B * (B - A))
        assert row["p_cubed_coefficient"] == F(A * B * (B - A), g)
    B = record["strongest_pair"]["B"]
    for branch in record["fixed_factor_cutoffs"]:
        a = branch["a"]
        L = (B * a - 1) // A
        D = B * a - A * L
        bound = F(a * L * (L - a), D)
        assert L == branch["L"] and D == branch["D"]
        assert bound == F(branch["max_q_squared"])
        q0 = branch["exclude_all_q_ge"]
        assert (q0 - 1) ** 2 <= bound < q0 * q0


def squarefree(n):
    result = 1
    prime = 2
    while prime * prime <= n:
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if exponent % 2:
            result *= prime
        prime += 1
    return result * n


valid = 0
reduced = 0
for A in range(1, 13):
    for q in range(1, 7):
        M = A * q * q
        for a in range(1, isqrt(M) + 1):
            if M % a or a * a == M:
                continue
            p = M // a - a
            if gcd(p, q) == 1:
                # prime support, not necessarily squarefree(A), is the condition.
                sf = squarefree(a)
                assert A % gcd(A, sf) == 0 and gcd(A, sf) == sf
                reduced += 1
            for B in range(A + 1, 21):
                s = isqrt(p * p + 4 * B * q * q)
                if s * s != p * p + 4 * B * q * q:
                    continue
                c = (s - p) // 2
                D = B * a - A * c
                g = gcd(A, B)
                assert c > a and D > 0 and D % g == 0
                assert q * q * D == a * c * (c - a)
                assert F(a**3) > F(A * A * g * q * q, B * (B - A))
                assert F(p**3) < F(A * B * (B - A) * q**4, g)
                L = (B * a - 1) // A
                assert F(q * q) <= F(a * L * (L - a), B * a - A * L)
                valid += 1
# Non-strict rejection at the cutoff would lose this valid pair.
A, B, q, a, p, c = 2, 6, 1, 1, 1, 2
L = (B * a - 1) // A
assert a * (a + p) == A * q * q and c * (c + p) == B * q * q
assert q * q == F(a * L * (L - a), B * a - A * L)
# Reducedness is essential to prime-support filtering.
A, q, a, p = 3, 2, 2, 4
assert a * (a + p) == A * q * q and gcd(p, q) > 1 and A % squarefree(a) != 0
out = {
    "actual_class_constants_and_cutoffs": "verified",
    "toy_valid_two_row_pairs": valid,
    "toy_reduced_squareclass_cases": reduced,
    "negative_controls": [
        "rejecting equality loses valid A2 B6 q1 a1 p1 c2",
        "dropping reducedness invalidates squareclass rule",
    ],
    "scope": "Exact finite replay plus independently inspected all-q algebra; bounds grow withq, do not boundq globally or classify all rational points.",
}
(P / "critic_gap_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
