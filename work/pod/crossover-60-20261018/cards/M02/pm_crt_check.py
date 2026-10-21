"""Independent CRT intersection replay; finite tests, not the universal theorem."""

import json
from collections import Counter
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = 720
prefix = [(4, 0), (6, 1), (10, 0), (12, 3), (16, 2), (18, 3), (30, 2), (36, 9)]
checks = 0
wrong_g_witness = None
for depth in range(len(prefix) + 1):
    U = {x for x in range(P) if all(x % m != a for m, a in prefix[:depth])}
    for m in (4, 6, 10, 12, 16, 18, 30, 36, 42, 60, 70, 72, 100, 126, 180, 210, 330):
        g = gcd(P, m)
        period = lcm(P, m)
        c = Counter(x % g for x in U)
        actual = Counter(x % m for x in range(period) if x % P in U)
        for a in range(m):
            assert actual[a] == c[a % g]
            assert Fraction(actual[a], period) == Fraction(g * c[a % g], P * m)
            checks += 1
            wrong = sum(x % m == a for x in U)
            if wrong != actual[a] and wrong_g_witness is None:
                wrong_g_witness = dict(
                    depth=depth, modulus=m, residue=a, actual=actual[a], wrong=wrong
                )
assert wrong_g_witness
result = {
    "crt_residue_checks": checks,
    "wrong_gcd_rejected_witness": wrong_g_witness,
    "scope": "Finite direct enumeration verifies formula on selected arbitrary-prefix states; no universal CRT proof.",
}
(HERE / "pm_crt_check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
