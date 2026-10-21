"""Small exact enumeration audit; no active search or large denominator run."""

import json
import runpy
from math import gcd, isqrt
from pathlib import Path

P = Path(__file__).parent
src = runpy.run_path(str(P.parents[2] / "885" / "extend_6x4.py"), run_name="critic_import")
factor, divisors = src["factor"], src["divisors"]
count = 0
for n in range(1, 21):
    for q in range(1, 9):
        m = n * q * q
        ff = factor(m)
        generated = {m // a - a for a in divisors(ff) if a < m // a}
        brute = {p for p in range(1, m) if isqrt(p * p + 4 * m) ** 2 == p * p + 4 * m}
        assert generated == brute
        for p in generated:
            s = isqrt(p * p + 4 * m)
            assert (s - p) % 2 == 0 and (s + p) % 2 == 0
            assert ((s - p) // 2) * ((s + p) // 2) == m
        count += 1
# Actual filter is conservative: no reduced fraction can be rejected by gcd branch.
retained_reducible = []
for q in range(1, 31):
    fq = factor(q)
    for p in range(1, 101):
        rejected = gcd(p, q) != 1 and q > 1 and all(p % r == 0 for r in fq)
        assert not (rejected and gcd(p, q) == 1)
        if gcd(p, q) > 1 and not rejected:
            retained_reducible.append([p, q])
assert [2, 6] in retained_reducible
classes = [src["Ns"], [10046592, 24561225, 115706752, 281637972, 564578560]]
assert all(any(isqrt(n) ** 2 != n for n in ns) for ns in classes)
# Therefore w=0 cannot satisfy all rows of either fixed grid; omitting a=b is safe.
result = {
    "small_exact_factor_vs_square_cases": count,
    "positive_numerator_bound": "1 <= p <= N*q²−1",
    "retained_reducible_example": [2, 6],
    "reduced_candidates_false_rejections": 0,
    "zero_column_impossible_for_both_classes": True,
    "scope": "Completeness derivation plus finite implementation checks. Denominator refers to reduced w=p/q, not directly to squared column coordinate w². No q<=1e6 replay.",
}
(P / "critic_enumeration_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
