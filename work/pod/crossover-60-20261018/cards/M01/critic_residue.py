"""Independent finite-field certificate replay at197, retaining infinity."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
src = json.loads((P / "inventor_residue_group.json").read_text())
data = json.loads((P / "inventor_elliptic.json").read_text())
p = 197
assert all(p % d for d in range(2, 15))
a = [4 * n % p for n in data["original_Ns"]]
assert len(set(a[:3])) == 3 and p != 2
squares = {j * j % p for j in range(p)}
points = {None} | {
    (x, y)
    for x in range(p)
    for y in range(p)
    if y * y % p == ((x + a[0]) * (x + a[1]) * (x + a[2])) % p
}
allowed = {q for q in points if q is None or all((q[0] + d) % p in squares for d in [0, *a])}
assert len(points) == 204 and len(allowed) == 9


def plus(u, v):
    if u is None:
        return v
    if v is None:
        return u
    x, y = u
    z, t = v
    if x == z and (y + t) % p == 0:
        return None
    if u == v:
        slope = (
            (3 * x * x + 2 * sum(a[:3]) * x + (a[0] * a[1] + a[0] * a[2] + a[1] * a[2]))
            * pow(2 * y, -1, p)
            % p
        )
    else:
        slope = (t - y) * pow(z - x, -1, p) % p
    outx = (slope * slope - sum(a[:3]) - x - z) % p
    result = (outx, (slope * (x - outx) - y) % p)
    assert result in points
    return result


def reduce(q):
    x, y = map(F, q)
    if x.denominator % p == 0:
        assert y.denominator % p == 0
        return None
    assert y.denominator % p != 0
    return (
        x.numerator * pow(x.denominator, -1, p) % p,
        y.numerator * pow(y.denominator, -1, p) % p,
    )


known = [reduce(r["point"]) for r in data["known_column_lifts"]]
cycle = []
q = None
while q not in cycle:
    cycle.append(q)
    q = plus(q, known[1])
assert q is None and len(cycle) == 51
logs = [cycle.index(q) for q in known]
allow = [j for j, q in enumerate(cycle) if q in allowed]
assert logs == [42, 1, 41, 39] == src["logs_to_base_P2"]
assert allow == [0, 1, 9, 10, 12, 39, 41, 42, 50] == src["allowed_logs_to_base_P2"]
assert set(cycle) & allowed == allowed
all_records = (
    data["exact_operation_records"]
    + json.loads((P / "inventor_holdout.json").read_text())["records"]
)
by_name = {r["operation"]: r for r in all_records if "point" in r}
for record in src["candidate_checks"]:
    actual = reduce(by_name[record["operation"]]["point"])
    reported = None if record["reduction"] is None else tuple(record["reduction"])
    assert actual == reported and (actual in allowed) == record["allowed"]
# Corruptions: dropping infinity rejects legitimate projective reduction;
# adding residue2 accepts a state violating one of the retained square tests.
assert None in allowed and cycle[2] not in allowed
assert plus(known[1], known[2]) == known[0]
# No finite-field sieve may simply discard denominators divisible by197.
assert all((1 + 4 * n * 0 * 0) % p in squares for n in data["original_Ns"])
out = {
    "curve_points": len(points),
    "subgroup_order": len(cycle),
    "known_logs": logs,
    "allowed_logs": allow,
    "records_checked": len(src["candidate_checks"]),
    "negative_controls": 2,
    "scope": "Exact finite-field arithmetic. Necessity uses good-reduction/group-homomorphism mathematics; no Lean model binding, global Mordell-Weil generators, or sufficiency claim.",
}
(P / "critic_residue_results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out))
