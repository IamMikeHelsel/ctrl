"""Exploratory conditional coverage bounds; output is NOT a Lean certificate.

AI-assisted research, 2026-10-18. Independent implementation. A Fermat filter
only removes certified composites, so pseudoprimes weaken rather than invalidate
the upper bound. The geometric complement includes every omitted smooth number.
"""

import argparse
import json
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path
from time import monotonic


def validate(primes, caps, prefix):
    if not primes or primes[0] != 2 or primes != sorted(set(primes)):
        raise ValueError("prime support must be increasing, distinct, and begin with2")
    if any(p < 2 or any(p % q == 0 for q in range(2, int(p**0.5) + 1)) for p in primes):
        raise ValueError("support contains a composite")
    if len(primes) != len(caps) or any(c < 0 for c in caps) or caps[0] < 1:
        raise ValueError("caps must match the support and include a positive2-exponent")
    if not prefix or len(set(prefix)) != len(prefix) or any(m < 4 for m in prefix):
        raise ValueError("prefix must be nonempty, distinct, and have moduli>=4")


def pool_bound(primes, caps):
    """All even smooth numbers in an exponent box, plus an exact infinite tail."""
    total = prod(Fraction(p, p - 1) for p in primes[1:])
    box = (1 - Fraction(1, 2 ** caps[0])) * prod(
        Fraction(p, p - 1) * (1 - Fraction(1, p ** (c + 1)))
        for p, c in zip(primes[1:], caps[1:], strict=True)
    )
    kept = []
    powers = [[2**a for a in range(1, caps[0] + 1)]] + [
        [p**a for a in range(c + 1)] for p, c in zip(primes[1:], caps[1:], strict=True)
    ]
    for factors in product(*powers):
        m = prod(factors)
        if m >= 4 and all(pow(a, m, m + 1) == 1 for a in (2, 3)):
            kept.append(m)
    return sorted(kept), total - box


def probe(primes, caps, prefix, node_limit, seconds=0):
    started = monotonic()
    validate(primes, caps, prefix)
    pool, tail = pool_bound(primes, caps)
    if not set(prefix) <= set(pool):
        raise ValueError(
            f"prefix not in admissible exponent box: {sorted(set(prefix) - set(pool))}"
        )
    period = lcm(*prefix)
    mass = {}
    for m in pool:
        if m not in prefix:
            g = gcd(m, period)
            mass[g] = mass.get(g, Fraction()) + Fraction(1, m)
    denominator = lcm(tail.denominator, *(v.denominator for v in mass.values()))
    weights = {g: int(v * denominator) * g for g, v in mass.items()}
    tail_scaled = int(tail * denominator) * period
    all_bits = (1 << period) - 1
    masks = {}
    for m in set(prefix) | set(mass):
        basic = all_bits // ((1 << m) - 1)
        masks[m] = [basic << a for a in range(m)]
    stats = {"nodes": 0, "pruned": 0, "unresolved": 0, "memo_hits": 0}
    seen = set()
    stabilizers = [1]
    for m in prefix:
        stabilizers.append(lcm(stabilizers[-1], m))
    worst = Fraction(-1)
    worst_assignment = []
    minimum_prune_gap = None

    def visit(depth, uncovered, assignments):
        nonlocal worst, worst_assignment, minimum_prune_gap
        key = (depth, uncovered)
        if key in seen:
            stats["memo_hits"] += 1
            return
        seen.add(key)
        stats["nodes"] += 1
        if stats["nodes"] > node_limit:
            raise TimeoutError("node_limit")
        if seconds and stats["nodes"] % 100 == 0 and monotonic() - started > seconds:
            raise TimeoutError("time_limit")
        count = uncovered.bit_count()
        upper = tail_scaled
        for g, weight in weights.items():
            upper += weight * max((uncovered & mask).bit_count() for mask in masks[g])
        for m in prefix[depth:]:
            upper += denominator * max((uncovered & mask).bit_count() for mask in masks[m])
        # Prefix class counts are integers; the common denominator scales them.
        if upper < count * denominator:
            stats["pruned"] += 1
            gap = Fraction(count * denominator - upper, denominator * period)
            minimum_prune_gap = gap if minimum_prune_gap is None else min(minimum_prune_gap, gap)
            return
        if depth == len(prefix):
            stats["unresolved"] += 1
            excess = Fraction(upper - count * denominator, denominator * period)
            if excess > worst:
                worst, worst_assignment = excess, assignments
            return
        m = prefix[depth]
        # Translation by the previous lcm fixes every previously assigned class.
        # Its orbits on residues modulo m are represented by 0 .. gcd(lcm,m)-1.
        for a in range(gcd(stabilizers[depth], m)):
            visit(depth + 1, uncovered & ~masks[m][a], assignments + [(m, a)])

    completion = "complete"
    try:
        visit(0, all_bits, [])
    except TimeoutError as exc:
        completion = str(exc)
    return {
        "primes": primes,
        "caps": caps,
        "prefix": prefix,
        "period": period,
        "retained_count": len(pool),
        "density_upper": str(sum((Fraction(1, m) for m in pool), tail)),
        "density_upper_float": float(sum((Fraction(1, m) for m in pool), tail)),
        "tail": str(tail),
        "tail_float": float(tail),
        "stats": stats,
        "completion": completion,
        "excluded_by_python_bound": completion == "complete" and stats["unresolved"] == 0,
        "minimum_prune_gap": str(minimum_prune_gap),
        "worst_unresolved_excess": str(worst),
        "worst_assignment": worst_assignment,
        "elapsed_seconds": monotonic() - started,
        "trust": "exact Python arithmetic; not Lean checked; not a solution of273",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", default="2,3,5,7")
    parser.add_argument("--caps", default="14,9,6,5")
    parser.add_argument("--prefix", default="4,6,10,12,16,18")
    parser.add_argument("--node-limit", type=int, default=1_000_000)
    parser.add_argument("--seconds", type=int, default=0)
    parser.add_argument("--output", default="smooth-probe.json")
    args = parser.parse_args()
    result = probe(
        [int(x) for x in args.primes.split(",")],
        [int(x) for x in args.caps.split(",")],
        [int(x) for x in args.prefix.split(",")],
        args.node_limit,
        args.seconds,
    )
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
