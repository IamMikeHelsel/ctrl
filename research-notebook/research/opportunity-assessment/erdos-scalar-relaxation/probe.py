#!/usr/bin/env python3
"""Exact rational obstruction to lowering the current scalar relaxation to .02586.

This is a relaxation witness, not a triangle-free graph or a Lean proof.
Run with Python 3 standard library; output contains only exact fractions.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
bridge = here.parent / "erdos-completion-spike"
c = F(7797, 10000)
I = F(2, 47)
x = 1 - 1 / (2 * c)
Q = 3 * x**2 / 2 - 5 * x / 4 + F(9, 32)
beta = c**2 * (I + Q) / (1 + c**2)
q = beta - Q
j = I - q
checks = {
    "oriented_cut_range": F(1, 3) <= x <= F(1, 2),
    "first_envelope_branch": x <= F(3, 8),
    "positive_c_at_current_threshold": 0 < c == F(7797, 10000),
    "normalization": 2 * c * (1 - x) == 1,
    "nonnegative_internal_edge_densities": q >= 0 and j >= 0,
    "BCL_cut_bound": q + j == I,
    "uniform_side_bound": beta == c**2 * j,
    "completion_restoration_bound": beta == Q + q,
    "cap_bound": beta <= I * c**2,
    "exceeds_0_02586": beta > F(2586, 100000),
    "below_checked_0_02587": beta < F(2587, 100000),
}
assert all(checks.values())
out = {
    "scope": "Exact rational feasible point of the current two-cut scalar relaxation",
    "values": {k: str(v) for k, v in dict(c=c, I=I, x=x, Q=Q, beta=beta, q=q, j=j).items()},
    "checks": checks,
    "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [
        bridge / "CutScalar.lean", bridge / "FixedCutBound.lean", bridge / "ScalarCertificate.lean"]},
    "conclusion": "These scalar hypotheses alone cannot force beta <= 2586/100000. A stronger graph inequality or construction is needed for that target.",
    "not_claimed": ["graph realizability", "counterexample to Erdos128", "optimal scalar constant", "novel theorem", "Lean-checked witness"],
}
print(json.dumps(out, indent=2))
