"""Elliptic coefficient-class sieve at fixed good prime197."""

import json
from fractions import Fraction as F
from math import gcd, lcm
from pathlib import Path

here = Path(__file__).parent
data = json.loads((here / "inventor_elliptic.json").read_text())
p = 197
A = [4 * n % p for n in data["original_Ns"]]
assert len(set(A[:3])) == 3
b2, b4 = sum(A[:3]) % p, (A[0] * A[1] + A[0] * A[2] + A[1] * A[2]) % p
squares = {x * x % p for x in range(p)}


def add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x, y = P
    z, v = Q
    if x == z and (y + v) % p == 0:
        return None
    m = (
        ((3 * x * x + 2 * b2 * x + b4) * pow(2 * y, -1, p)) % p
        if P == Q
        else ((v - y) * pow(z - x, -1, p)) % p
    )
    X = (m * m - b2 - x - z) % p
    Y = (-y + m * (x - X)) % p
    assert Y * Y % p == (X + A[0]) * (X + A[1]) * (X + A[2]) % p
    return (X, Y)


def reduce_point(P):
    x, y = map(F, P)
    denominator = lcm(x.denominator, y.denominator)
    coords = [
        x.numerator * (denominator // x.denominator),
        y.numerator * (denominator // y.denominator),
        denominator,
    ]
    common = gcd(gcd(abs(coords[0]), abs(coords[1])), coords[2])
    X, Y, Z = [value // common % p for value in coords]
    if Z == 0:
        assert X == 0 and Y != 0
        return None
    return (X * pow(Z, -1, p) % p, Y * pow(Z, -1, p) % p)


def order(P):
    Q = None
    for n in range(1, 2 * p + 2):
        Q = add(Q, P)
        if Q is None:
            return n
    raise AssertionError("group order bound unexpectedly exceeded")


def allowed(P):
    return P is None or all((P[0] + shift) % p in squares for shift in [0] + A)


known = [reduce_point(r["point"]) for r in data["known_column_lifts"]]
assert add(known[1], known[2]) == known[0]
generators = known[1:]
subgroup = {None}
frontier = [None]
while frontier:
    Q = frontier.pop()
    for generator in generators:
        S = add(Q, generator)
        if S not in subgroup:
            subgroup.add(S)
            frontier.append(S)
allowed_states = [S for S in subgroup if allowed(S)]
E = [None] + [
    (x, y)
    for x in range(p)
    for y in range(p)
    if y * y % p == (x + A[0]) * (x + A[1]) * (x + A[2]) % p
]
assert len(E) % len(subgroup) == 0
assert all(allowed(P) for P in known)
cycle = []
Q = None
for _ in range(order(known[1])):
    cycle.append(Q)
    Q = add(Q, known[1])
assert set(cycle) == subgroup
known_logs = [cycle.index(P) for P in known]
allowed_logs = [i for i, P in enumerate(cycle) if allowed(P)]
all_allowed = [P for P in E if allowed(P)]
assert set(all_allowed) == set(allowed_states)
partial_states = [P for P in E if P is None or all((P[0] + v) % p in squares for v in A[:3])]
assert set(partial_states) == subgroup
gate_counts = {"curve": len(E), "first_three_rows": len(partial_states)}
for name, shift in [("plus_X", 0), ("plus_row_four", A[3]), ("plus_row_five", A[4])]:
    partial_states = [P for P in partial_states if P is None or (P[0] + shift) % p in squares]
    gate_counts[name] = len(partial_states)
assert set(partial_states) == set(all_allowed)
# Verify every finite discovery/holdout candidate's residue membership matches
# the actual complete-squares necessary test. Infinity remains allowed.
candidate_checks = []
allrecords = (
    data["exact_operation_records"]
    + json.loads((here / "inventor_holdout.json").read_text())["records"]
)
for row in allrecords:
    if "point" not in row:
        continue
    Q = reduce_point(row["point"])
    if row["operation"].startswith("P") and "+T" in row["operation"]:
        continue
    assert Q in subgroup
    candidate_checks.append({"operation": row["operation"], "reduction": Q, "allowed": allowed(Q)})
result = {
    "prime": p,
    "good_reduction_distinct_first_three_shifts": A[:3],
    "full_finite_curve_order": len(E),
    "known_points_reduction": known,
    "known_point_orders": [order(P) for P in known],
    "logs_to_base_P2": known_logs,
    "allowed_logs_to_base_P2": allowed_logs,
    "complete_curve_allowed_count": len(all_allowed),
    "successive_gate_counts_including_infinity": gate_counts,
    "generators": "P2,P3,P4; P1=P2+P3 is already dependent",
    "generated_subgroup_order": len(subgroup),
    "allowed_subgroup_state_count": len(allowed_states),
    "allowed_subgroup_states": sorted(allowed_states, key=lambda P: (-1, -1) if P is None else P),
    "candidate_checks": candidate_checks,
    "next_test": "Use finite group additions to reject coefficient triples whose residue state is not allowed BEFORE evaluating rational combinations. Combine another good prime only after preserving the infinity branch and independently replaying the reduction map.",
    "limits": "This filters only combinations of the supplied points and does not establish they generate the Mordell-Weil group. Allowed residue classes are necessary, not sufficient; infinity survives. No fifth column or global nonextension proof.",
}
(here / "inventor_residue_group.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            key: result[key]
            for key in [
                "full_finite_curve_order",
                "known_point_orders",
                "generated_subgroup_order",
                "allowed_subgroup_state_count",
                "allowed_subgroup_states",
            ]
        },
        indent=2,
    )
)
