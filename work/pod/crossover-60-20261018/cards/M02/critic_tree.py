"""Independent exact mass/tree reconstruction and consumed-certificate mutations."""

import json
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
P = (2, 3, 5, 7, 11)
CAPS = (14, 9, 6, 5, 4)
PREFIX = (4, 6, 10, 12, 16, 18, 30, 36)
L = 720
# Disjoint first-outside-coordinate tail, not total-minus-box.
finite = [
    sum((Q(1, p**k) for k in range(1 if i == 0 else 0, c + 1)), Q())
    for i, (p, c) in enumerate(zip(P, CAPS, strict=True))
]
infinite = [Q(1) if i == 0 else Q(p, p - 1) for i, p in enumerate(P)]
tail = sum(
    (
        prod(finite[:i]) * Q(1, P[i] ** CAPS[i] * (P[i] - 1)) * prod(infinite[i + 1 :])
        for i in range(5)
    ),
    Q(),
)
assert tail == Q(1806085527193, 7116137582400000)
values = []
for exponents in product(range(1, 15), range(10), range(7), range(6), range(5)):
    m = prod(p**e for p, e in zip(P, exponents, strict=True))
    if m >= 4 and pow(2, m, m + 1) == pow(3, m, m + 1) == 1:
        values.append(m)
assert len(values) == len(set(values)) == 5265
mass = {}
for m in values:
    if m not in PREFIX:
        g = gcd(m, L)
        mass[g] = mass.get(g, Q()) + Q(1, m)
D = lcm(tail.denominator, *(x.denominator for x in mass.values()))
assert all((x * D).denominator == 1 for x in mass.values())
weights = {g: int(v * D) * g for g, v in mass.items()}
# Explicit residue enumeration avoids source's geometric bit-mask formula.
masks = {
    g: [sum(1 << x for x in range(r, L, g)) for r in range(g)] for g in set(mass) | set(PREFIX)
}
FULL = (1 << L) - 1
stabilizers = [1]
for m in PREFIX:
    stabilizers.append(lcm(stabilizers[-1], m))


def bound(depth, U):
    return (
        int(tail * D) * L
        + sum(w * max((U & mask).bit_count() for mask in masks[g]) for g, w in weights.items())
        + D * sum(max((U & mask).bit_count() for mask in masks[m]) for m in PREFIX[depth:])
    )


def key(depth, U):
    return str(depth) + ":" + hex(U)


def rotate(U, n):
    n %= L
    return ((U << n) | (U >> (L - n))) & FULL


nodes = {}
memo = 0
orbit_checks = 0


def build(depth, U):
    global memo, orbit_checks
    ident = key(depth, U)
    if ident in nodes:
        memo += 1
        return ident
    upper = bound(depth, U)
    row = {"depth": depth, "U": hex(U), "upper": str(upper), "children": []}
    nodes[ident] = row
    if upper < U.bit_count() * D:
        return ident
    assert depth < len(PREFIX)
    m = PREFIX[depth]
    old = stabilizers[depth]
    g = gcd(m, old)
    assert rotate(U, old) == U
    for r in range(m):
        c = r % g
        shift = next(k * old for k in range(m // g) if (c + k * old) % m == r)
        assert rotate(U & ~masks[m][c], shift) == U & ~masks[m][r]
        orbit_checks += 1
    for r in range(g):
        row["children"].append(build(depth + 1, U & ~masks[m][r]))
    return ident


root = build(0, FULL)


def verify(cert):
    checked = set()

    def visit(ident, depth, U):
        assert ident == key(depth, U)
        if ident in checked:
            return
        checked.add(ident)
        row = cert[ident]
        assert row["depth"] == depth and int(row["U"], 16) == U
        upper = bound(depth, U)
        assert int(row["upper"]) == upper
        if upper < U.bit_count() * D:
            assert not row["children"]
            return
        assert depth < len(PREFIX)
        m = PREFIX[depth]
        g = gcd(stabilizers[depth], m)
        expected = [key(depth + 1, U & ~masks[m][r]) for r in range(g)]
        assert row["children"] == expected
        for child, r in zip(row["children"], range(g), strict=True):
            visit(child, depth + 1, U & ~masks[m][r])

    visit(root, 0, FULL)
    return len(checked)


assert verify(nodes) == 3518
pruned = [r for r in nodes.values() if not r["children"]]
gap = min(Q(int(r["U"], 16).bit_count() * D - int(r["upper"]), D * L) for r in pruned)
assert gap == Q(50661803066306609, 1239915812357376000000)
rejected = []
for name in ["missing_branch", "fake_prune", "wrong_state", "decreased_capacity"]:
    cert = deepcopy(nodes)
    if name == "missing_branch":
        cert[root]["children"].pop()
    elif name == "fake_prune":
        cert[root]["children"] = []
        cert[root]["upper"] = "0"
    elif name == "wrong_state":
        cert[cert[root]["children"][0]]["U"] = "0x1"
    else:
        cert[next(k for k, r in cert.items() if not r["children"])]["upper"] = "0"
    try:
        verify(cert)
    except (AssertionError, KeyError):
        rejected.append(name)
    else:
        raise AssertionError(name)


def verify_payload(payload):
    # Bind the consumed tail field to a separately derived disjoint geometric sum.
    # This value is recomputed from the model, not an expected literal or a keyword guard.
    derived = sum(
        (
            prod(finite[:i]) * Q(1, P[i] ** CAPS[i] * (P[i] - 1)) * prod(infinite[i + 1 :])
            for i in range(5)
        ),
        Q(),
    )
    assert Q(payload["tail"]) == derived
    return verify(payload["nodes"])


payload = {"tail": str(tail), "nodes": nodes}
assert verify_payload(payload) == 3518
for mutation in ["omitted_depth", "underestimated_tail"]:
    damaged = deepcopy(payload)
    if mutation == "omitted_depth":
        del damaged["nodes"][root]["depth"]
    else:
        damaged["tail"] = str(tail / 2)
    try:
        verify_payload(damaged)
    except (AssertionError, KeyError):
        rejected.append(mutation)
    else:
        raise AssertionError(mutation)
(HERE / "critic_tree_payload.json").write_text(json.dumps(payload, separators=(",", ":")) + "\n")

result = {
    "nodes": len(nodes),
    "pruned": len(pruned),
    "memo_hits": memo,
    "explicit_orbit_equivalences": orbit_checks,
    "tail_disjoint_first_outside": str(tail),
    "minimum_gap": str(gap),
    "pool_size": len(values),
    "unconditioned_mass": str(sum((Q(1, m) for m in values), tail)),
    "rejected_actual_certificate_mutations": rejected,
    "scope": "Exact Python reconstruction and certificate consumer; no complete Lean finite-history proof.",
}
(HERE / "critic_tree.json").write_text(json.dumps(result, indent=2) + "\n")
(HERE / "critic_tree_certificate.json").write_text(json.dumps(nodes, separators=(",", ":")) + "\n")
print(json.dumps(result, indent=2))
