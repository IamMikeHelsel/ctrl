"""Exact full-state septic candidate and Bernstein enclosure, not complete feasibility."""

import json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent


def solve(m, b):
    a = [r[:] + [v] for r, v in zip(m, b, strict=True)]
    for k in range(len(a)):
        pivot = next(i for i in range(k, len(a)) if a[i][k])
        a[k], a[pivot] = a[pivot], a[k]
        z = a[k][k]
        a[k] = [x / z for x in a[k]]
        for i in range(len(a)):
            if i != k:
                z = a[i][k]
                a[i] = [x - z * y for x, y in zip(a[i], a[k], strict=True)]
    return [r[-1] for r in a]


def derivative(c):
    return [i * c[i] for i in range(1, len(c))]


def bern(c):
    n = len(c) - 1
    return [
        sum((c[k] * F(comb(i, k), comb(n, k)) for k in range(i + 1)), F(0)) for i in range(n + 1)
    ]


def split(b):
    layers = [b]
    while len(layers[-1]) > 1:
        layers.append([(x + y) / 2 for x, y in zip(layers[-1][:-1], layers[-1][1:], strict=True)])
    return [row[0] for row in layers], [row[-1] for row in layers[::-1]]


def evaluate(c, x):
    return sum((v * x**i for i, v in enumerate(c)), F(0))


def screen(c, lo, hi):
    # Only promote enclosing leaves; any violation is an exact point witness.
    stack = [(bern(c), F(0), F(1), 0)]
    accepted = 0
    while stack:
        b, l, r, d = stack.pop()
        if min(b) >= lo and max(b) <= hi:
            accepted += 1
            continue
        mid = (l + r) / 2
        v = evaluate(c, mid)
        if v < lo or v > hi:
            return {
                "decision": "candidate_rejected",
                "time_fraction": str(mid),
                "value": str(v),
                "bounds": [str(lo), str(hi)],
            }
        if d == 12:
            return {"decision": "UNKNOWN", "reason": "enclosurebudget"}
        left, right = split(b)
        stack.extend([(left, l, mid, d + 1), (right, mid, r, d + 1)])
    return {"decision": "candidate_certified", "leaves": accepted}


T = F(249, 200)
start = [F(44217, 1600000), F(2601, 8000), F(51, 20), F(10)]
end = [F(3, 5), F(0), F(0), F(0)]
c = [start[k] * T**k / factorial(k) for k in range(4)]
m = [[F(factorial(i), factorial(i - k)) for i in range(4, 8)] for k in range(4)]
rhs = [
    end[k] * T**k - sum((c[i] * F(factorial(i), factorial(i - k)) for i in range(k, 4)), F(0))
    for k in range(4)
]
c += solve(m, rhs)
cur = c[:]
receipts = []
for k, (lo, hi) in enumerate(
    [(F(0), F(3, 5)), (F(0), F(1)), (F(-3), F(3)), (F(-10), F(10)), (F(-400), F(400))]
):
    scaled = [x / T**k for x in cur]
    if k < 4:
        assert evaluate(scaled, 0) == start[k] and evaluate(scaled, 1) == end[k]
    receipts.append({"order": k, **screen(scaled, lo, hi)})
    cur = derivative(cur)
out = {
    "source_execution_state": [str(x) for x in start],
    "duration": str(T),
    "coefficients": [str(x) for x in c],
    "checks": receipts,
    "scope": "Onefullstatepolynomial candidate only. Rejectedcandidate notinfeasibletask; existingpiecewise source witness remainsvalid. Bernsteinimplementation is exactPython, notkernelcertificate.",
}
(HERE / "pm_hermite.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(receipts, indent=2))
