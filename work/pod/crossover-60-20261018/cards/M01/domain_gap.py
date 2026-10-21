"""All-denominator gap formulas; exact checks and toy negative controls only."""

import json
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path

CLASSES = [
    (206222625, [677376000, 2019635200, 4786481700, 16670745700], [13440, 75936, 129360, 279840]),
    (24561225, [115706752, 281637972, 564578560], [5976, 10104, 24216, 69624]),
]


def squarefree_part(n):
    out = 1
    prime = 2
    while prime * prime <= n:
        parity = 0
        while n % prime == 0:
            parity ^= 1
            n //= prime
        if parity:
            out *= prime
        prime += 1
    return out * n


def constants(A, B):
    g = gcd(A, B)
    return g, F(A * A * g, B * (B - A)), A * B * (B - A) // g


def gap(A, B, a):
    # largest integer strictly less than B*a/A
    L = (B * a - 1) // A
    D = B * a - A * L
    assert 0 < D <= A and D % gcd(A, B) == 0
    return L, D, F(a * L * (L - a), D)


def validate(A, B, q, a, p, c):
    assert A < B and min(a, p, c, q) > 0
    assert a * (a + p) == A * q * q
    assert c * (c + p) == B * q * q
    g, Ka, Kp = constants(A, B)
    D = B * a - A * c
    assert a < c and 0 < D and D % g == 0
    assert q * q * D == a * c * (c - a)
    assert a**3 > Ka * q * q
    assert p**3 < Kp * q**4
    L, _, threshold = gap(A, B, a)
    assert c <= L and q * q <= threshold


def main():
    records = []
    for A, Bs, ds in CLASSES:
        constants_rows = []
        for B in Bs:
            g, Ka, Kp = constants(A, B)
            for p in ds:
                sa, sc = isqrt(p * p + 4 * A), isqrt(p * p + 4 * B)
                assert sa * sa == p * p + 4 * A and sc * sc == p * p + 4 * B
                validate(A, B, 1, (sa - p) // 2, p, (sc - p) // 2)
            constants_rows.append(
                {"B": B, "gcd": g, "a_cubed_coefficient": str(Ka), "p_cubed_coefficient": Kp}
            )
        strongest = min(constants_rows, key=lambda v: v["p_cubed_coefficient"])
        B = strongest["B"]
        branches = []
        for a in [1, 2, 3, 10, 100, 1000]:
            L, D, threshold = gap(A, B, a)
            # All integer q >= this value are excluded for this fixed factor a.
            q0 = isqrt(threshold.numerator // threshold.denominator) + 1
            assert F(q0 * q0) > threshold
            if q0 > 1:
                assert F((q0 - 1) ** 2) <= threshold
            branches.append(
                {"a": a, "L": L, "D": D, "max_q_squared": str(threshold), "exclude_all_q_ge": q0}
            )
        records.append(
            {
                "A": A,
                "all_pair_bounds": constants_rows,
                "strongest_pair": strongest,
                "fixed_factor_cutoffs": branches,
            }
        )
    # Small toy instances, not a rerun of either 885 denominator search.
    valid = 0
    candidates = 0
    false_rejections = 0
    reduced_squareclass_checks = 0
    equality_examples = []
    for A in range(1, 21):
        for B in range(A + 1, 31):
            for q in range(1, 11):
                M = A * q * q
                for a in range(1, isqrt(M) + 1):
                    if M % a or a * a == M:
                        continue
                    p = M // a - a
                    candidates += 1
                    if gcd(p, q) == 1:
                        assert A % squarefree_part(a) == 0
                        reduced_squareclass_checks += 1
                    s = isqrt(p * p + 4 * B * q * q)
                    _, _, threshold = gap(A, B, a)
                    if s * s == p * p + 4 * B * q * q:
                        c = (s - p) // 2
                        validate(A, B, q, a, p, c)
                        valid += 1
                        false_rejections += q * q > threshold
                        if q * q == threshold and len(equality_examples) < 3:
                            equality_examples.append(
                                {"A": A, "B": B, "q": q, "a": a, "p": p, "c": c}
                            )
    assert false_rejections == 0 and equality_examples
    # Without reduced p/q, the square-class claim is false:
    # A=3,q=2,a=2,b=6,p=4; squarefreepart(a)=2 does not divide A.
    assert 2 * (2 + 4) == 3 * 2**2 and gcd(4, 2) != 1
    assert 3 % squarefree_part(2) != 0
    full_grids = [
        [206222625, 677376000, 2019635200, 4786481700, 16670745700],
        [10046592, 24561225, 115706752, 281637972, 564578560],
    ]
    all_pair_bounds = []
    for ns in full_grids:
        rows = [
            {"A": A, "B": B, "gcd": gcd(A, B), "p_cubed_coefficient": constants(A, B)[2]}
            for A, B in combinations(ns, 2)
        ]
        all_pair_bounds.append(
            {"pairs": rows, "best": min(rows, key=lambda r: r["p_cubed_coefficient"])}
        )
    result = {
        "classes": records,
        "global_all_pair_cubic_bounds": all_pair_bounds,
        "toy_candidates": candidates,
        "toy_valid_pairs": valid,
        "false_rejections": false_rejections,
        "reduced_squareclass_checks": reduced_squareclass_checks,
        "nonreduced_negative_control": {"A": 3, "q": 2, "a": 2, "p": 4},
        "boundary_equalities_must_not_reject": equality_examples,
        "scope": "Exact constants and finite checks of proved algebraic inequalities; no global non-extension, no actual-grid denominator scan",
    }
    Path(__file__).with_name("domain_gap_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
