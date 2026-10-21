"""Independent local13-smooth capacity reconstruction; no full search claim."""

import json
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = json.loads(
    Path("work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json").read_text()
)
P = source["primes"]
C = source["caps"]
L = source["period"]
prefix = dict(source["worst_assignment"])
pool = []
for es in product(*(range(1, c + 1) if i == 0 else range(c + 1) for i, c in enumerate(C))):
    m = prod(p**e for p, e in zip(P, es, strict=True))
    if m >= 4 and pow(2, m, m + 1) == pow(3, m, m + 1) == 1:
        pool.append(m)
assert len(pool) == 22944
finite = [
    sum((F(1, p**k) for k in range(1 if i == 0 else 0, c + 1)), F())
    for i, (p, c) in enumerate(zip(P, C, strict=True))
]
inf = [F(1) if i == 0 else F(p, p - 1) for i, p in enumerate(P)]
tail = sum(
    (prod(finite[:i]) * F(1, P[i] ** C[i] * (P[i] - 1)) * prod(inf[i + 1 :]) for i in range(6)), F()
)
assert tail == F(source["tail"])
mass = {}
for m in pool:
    if m not in prefix:
        g = gcd(m, L)
        mass[g] = mass.get(g, F()) + F(1, m)
D = lcm(tail.denominator, *(v.denominator for v in mass.values()))
weights = {g: int(v * D) * g for g, v in mass.items()}
masks = {
    g: [sum(1 << x for x in range(a, L, g)) for a in range(g)] for g in set(mass) | set(prefix)
}
U = sum(1 << x for x in range(L) if all(x % m != a for m, a in prefix.items()))
assert U.bit_count() == 1574


def excess(bits, removed):
    counts = {g: max((bits & m).bit_count() for m in masks[g]) for g in mass}
    return F(
        int(tail * D) * L
        + sum(w * counts[g] for g, w in weights.items())
        - D * sum(counts[m] for m in removed)
        - D * bits.bit_count(),
        D * L,
    )


base = excess(U, [])
assert base == F(source["worst_unresolved_excess"])
parents = {U & ~mask for mask in masks[42]}
assert len(parents) == 33
chosen = []
total = pruned = 0
worst = F(-1)
for parent in parents:
    opts = []
    for m in [40, 60]:
        children = {parent & ~mask for mask in masks[m]}
        vals = [excess(child, [42, m]) for child in children]
        opts.append((max(vals), m, len(vals), sum(v < 0 for v in vals)))
    option = min(opts)
    chosen.append(option[1])
    total += option[2]
    pruned += option[3]
    worst = max(worst, option[0])
inv = json.loads((HERE / "inventor_adaptive.json").read_text())
assert str(worst) == inv["comparison"]["adaptive_worst"]
assert (
    total == inv["comparison"]["adaptive_total_children"]
    and pruned == inv["comparison"]["adaptive_pruned_children"]
)
assert all(m == 60 for m in chosen)
# Dropping distinctness is genuinely false: four residue classes modulo4 cover every integer.
assert all(any(x % 4 == r for r in range(4)) for x in range(100))
result = {
    "pool": len(pool),
    "tail": str(tail),
    "saved_leaf_survivors": U.bit_count(),
    "base_excess": str(base),
    "parents": len(parents),
    "chosen60": len(chosen),
    "children": total,
    "pruned": pruned,
    "worst_excess": str(worst),
    "distinctness_counterexample": "all four residue classes modulo4 cover Z; each4+1 prime and11smooth, but repeated modulus violates premise",
    "scope": "One saved leaf only; positive capacity excess is failure of this bound, not a covering witness.",
}
(HERE / "critic_thirteen.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
# Independently reconstruct every pair from explicit restricted bit sets.
vertices = [40, 42, 60, 70, 72, 112]
gains = {}
for i, m in enumerate(vertices):
    for n in vertices[i + 1 :]:
        left = [U & bitset for bitset in masks[m]]
        right = [U & bitset for bitset in masks[n]]
        separate = max(x.bit_count() for x in left) + max(x.bit_count() for x in right)
        joint = max((x | y).bit_count() for x in left for y in right)
        gains[(m, n)] = F(separate - joint, L)
        row = next(r for r in inv["coupled_pair_bounds"] if r["moduli"] == [m, n])
        assert F(row["density_gain"]) == gains[(m, n)]


def matchings(remaining):
    if not remaining:
        yield []
        return
    head, *rest = remaining
    yield from matchings(rest)
    for other in rest:
        for following in matchings([v for v in rest if v != other]):
            yield [(head, other), *following]


all_matches = list(matchings(vertices))
assert len(all_matches) == 76
for pairs in all_matches:
    ends = [m for pair in pairs for m in pair]
    assert len(ends) == len(set(ends))
best = max(all_matches, key=lambda pairs: sum((gains[pair] for pair in pairs), F()))
saving = sum((gains[pair] for pair in best), F())
assert saving == F(13, 5040)
assert base - saving == F(333129815691682964686943, 8853308879184753984000000)
# Overlapping pair corrections fail for three identical singleton coverage sets:
# separate sum3 minus three pair savings1 gives0, but actual union has size1.
assert 3 - 3 * 1 < len({0} | {0} | {0})
result["disjoint_pair_check"] = {
    "matchings": len(all_matches),
    "all15gains_reproduced": True,
    "selected": best,
    "saving": str(saving),
    "residual_excess": str(base - saving),
    "overlapping_pair_correction_negative_control": True,
}
(HERE / "critic_thirteen.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result["disjoint_pair_check"], indent=2))
