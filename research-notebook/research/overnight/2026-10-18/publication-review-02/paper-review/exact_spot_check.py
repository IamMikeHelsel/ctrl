"""Independent rational checks of values printed in the reviewed paper.

This is a small paper audit, not a replacement for the separate Lean replay.
No builder numerical functions are imported.
"""
from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent
h = F(1, 5)
outward = [(F(11, 50), F(1, 50))]
immediate = outward + [(F(13, 25), -F(1, 50))]
deferred = outward + [(F(31, 50), -F(1, 50))]


def derivative(events, t, n):
    return sum(delta / h**n * sum(
        (-1)**k * comb(4, k) * max(F(0), (t-tau)/h-k)**(4-n)
        for k in range(5)) / factorial(4-n) for tau, delta in events)


def acceleration_candidates(events, current):
    knots = sorted({current} | {tau+k*h for tau, _ in events
                   for k in range(5) if tau+k*h >= current})
    candidates = knots[:]
    for left, right in zip(knots, knots[1:]):
        jl, jr = derivative(events, left, 3), derivative(events, right, 3)
        if jl != jr:
            stationary = left-jl*(right-left)/(jr-jl)
            if left < stationary < right:
                candidates.append(stationary)
    return sorted(candidates)


def determinant(a):
    n = len(a)
    total = F(0)
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        term = F((-1)**inversions)
        for i in range(n):
            term *= a[i][p[i]]
        total += term
    return total


def matmul(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


jet = [derivative(outward, F(13, 25), n) for n in range(4)]
assert jet == [F(77, 19200), F(23, 480), F(5, 16), -F(5, 4)]
assert derivative(deferred, F(1, 2), 0) == F(779, 250000)
assert all(derivative(deferred, F(71, 50), n) == 0 for n in range(4))
assert F(779, 250000)-2*F(1, 5000) >= F(1, 1000)
assert F(1, 100)+F(15, 2)/(48*10) == F(41, 1600) <= 2*10**2*F(1, 5000)

extrema = [(t, derivative(immediate, t, 2))
           for t in acceleration_candidates(immediate, F(13, 25))]
assert min(v for _, v in extrema) == -F(21, 32)
assert max(v for _, v in extrema) == F(1, 3)
assert derivative(immediate, F(77, 100), 2) == -F(21, 32)

Q = [[F(x, 1000) for x in row] for row in
     [[2162, -549, -234], [-549, 518, -151], [-234, -151, 810]]]
P = [[F(x, 68317631) for x in row] for row in
     [[49597375, 60003000, 25513875],
      [60003000, 212058000, 56866000],
      [25513875, 56866000, 102314375]]]
identity = [[F(int(i == j)) for j in range(3)] for i in range(3)]
assert matmul(Q, P) == identity == matmul(P, Q)
leading = [determinant([row[:k] for row in Q[:k]]) for k in range(1, 4)]
assert all(v > 0 for v in leading)
assert F(259, 500)*F(101, 100) < 4
assert F(81, 100)*F(101, 100) < 1

result = {
    "status": "PASS",
    "scope": "Exact printed reference values, reversal extrema, tracking budget, Q inverse and coordinate thresholds. No new all-time physical or optimality claim.",
    "revision_jet": list(map(str, jet)),
    "immediate_acceleration_candidates": [{"t": str(t), "a": str(v)} for t, v in extrema],
    "required_text_correction": "Acceleration magnitude reaches 21/32; actual acceleration is -21/32 at 0.77 seconds.",
    "Q_leading_principal_minors": list(map(str, leading)),
    "Q_times_P_and_P_times_Q": "exact identity",
}
(OUT / "exact-spot-check.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
