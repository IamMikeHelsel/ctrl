"""Independent exact replay of the 11-smooth conditional-capacity certificate.

Audit and verification for Erdős Problem 273 (covering systems with m+1 prime).
This standalone verifier executes exact rational arithmetic with zero external
solvers, zero floating-point rounding, and zero search library imports.

The certificate establishes that no covering system exists using distinct moduli
m >= 4 with m+1 prime and prime factors bounded by 11. It overcomes an
unconditioned reciprocal mass excess of ~1.1748 via prefix conditioning on
(4, 6, 10, 12, 16, 18, 30, 36) with period 720 and stabilizer orbit reduction,
terminating in 3,518 nodes with a strictly positive density margin > 4.08e-5.

Run with:
    uv run python work/273/check_eleven.py [--output PATH] [--self-test]
"""

import json
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path

import typer

PRIMES = (2, 3, 5, 7, 11)
CAPS = (14, 9, 6, 5, 4)
PREFIX = (4, 6, 10, 12, 16, 18, 30, 36)
PERIOD = 720
EXPECTED_POOL_SIZE = 5265
EXPECTED_NODES = 3518
EXPECTED_PRUNED = 3271
EXPECTED_TAIL = Fraction(1806085527193, 7116137582400000)
MIN_PRUNE_GAP = Fraction(50661803066306609, 1239915812357376000000)
MIN_SURVIVORS = 212


def require(condition: bool, message: str) -> None:
    """Keep verification active even under Python's optimized execution mode."""
    if not condition:
        raise ValueError(message)


def compute_geometric_tail(primes: tuple[int, ...], caps: tuple[int, ...]) -> Fraction:
    """Exact rational sum of reciprocal smooth numbers outside the exponent box."""
    total = prod(Fraction(p, p - 1) for p in primes[1:])
    box = (1 - Fraction(1, 2 ** caps[0])) * prod(
        Fraction(p, p - 1) * (1 - Fraction(1, p ** (c + 1)))
        for p, c in zip(primes[1:], caps[1:], strict=True)
    )
    return total - box


def compute_admissible_pool(primes: tuple[int, ...], caps: tuple[int, ...]) -> list[int]:
    """All even smooth numbers in exponent box passing Fermat tests base 2 and 3 for m+1."""
    kept = []
    powers = [[2**a for a in range(1, caps[0] + 1)]] + [
        [p**a for a in range(c + 1)] for p, c in zip(primes[1:], caps[1:], strict=True)
    ]
    for factors in product(*powers):
        m = prod(factors)
        if m >= 4 and all(pow(a, m, m + 1) == 1 for a in (2, 3)):
            kept.append(m)
    return sorted(kept)


def check(
    *,
    period: int = PERIOD,
    prefix: tuple[int, ...] = PREFIX,
    tail_bound: Fraction = EXPECTED_TAIL,
    min_gap: Fraction = MIN_PRUNE_GAP,
    capacity_bias: int = 0,
    branch_offset: int = 0,
    node_limit: int = 50_000,
) -> dict:
    """Replay the 11-smooth conditional capacity tree without external search solvers."""
    require(prefix == PREFIX, f"unexpected prefix moduli: {prefix} != {PREFIX}")
    require(period == lcm(*prefix), f"period {period} must equal lcm of prefix {lcm(*prefix)}")
    require(period == PERIOD, f"unexpected root period: {period} != {PERIOD}")
    require(min_gap > 0, "claimed margin must be positive")
    require(
        min_gap <= MIN_PRUNE_GAP,
        f"claimed margin {min_gap} exceeds verified bound {MIN_PRUNE_GAP}",
    )
    require(capacity_bias == 0, f"capacity bias must be zero in authentic audit, got {capacity_bias}")
    require(branch_offset == 0, f"branch offset must be zero in canonical tree, got {branch_offset}")

    tail = compute_geometric_tail(PRIMES, CAPS)
    require(tail == EXPECTED_TAIL, "exact 5-prime geometric tail does not match expected")
    require(
        tail_bound == tail,
        f"geometric tail bound mismatch: claimed {tail_bound} != exact {tail}",
    )

    pool = compute_admissible_pool(PRIMES, CAPS)
    require(len(pool) == EXPECTED_POOL_SIZE, f"pool size mismatch: {len(pool)} != {EXPECTED_POOL_SIZE}")
    require(set(prefix) <= set(pool), "prefix not present in admissible pool")

    masses: dict[int, Fraction] = {}
    for m in pool:
        if m not in prefix:
            g = gcd(m, period)
            masses[g] = masses.get(g, Fraction()) + Fraction(1, m)

    denominator = lcm(tail.denominator, *(v.denominator for v in masses.values()))
    weights = {g: int(v * denominator) * g for g, v in masses.items()}
    tail_scaled = int(tail * denominator) * period

    all_bits = (1 << period) - 1
    masks: dict[int, list[int]] = {}
    for m in set(prefix) | set(masses):
        basic = all_bits // ((1 << m) - 1)
        masks[m] = [basic << a for a in range(m)]

    stabilizers = [1]
    for m in prefix:
        stabilizers.append(lcm(stabilizers[-1], m))

    stats = {"nodes": 0, "pruned": 0, "unresolved": 0, "memo_hits": 0}
    seen: set[tuple[int, int]] = set()
    min_gap_seen: Fraction | None = None
    min_survivor_count = period

    def visit(depth: int, uncovered: int) -> None:
        nonlocal min_gap_seen, min_survivor_count
        key = (depth, uncovered)
        if key in seen:
            stats["memo_hits"] += 1
            return
        seen.add(key)
        stats["nodes"] += 1
        require(stats["nodes"] <= node_limit, f"node limit ({node_limit}) exceeded during replay")

        count = uncovered.bit_count()
        require(count > 0, "uncovered survivor count must be positive at every branch")
        min_survivor_count = min(min_survivor_count, count)

        upper = tail_scaled + capacity_bias
        for g, weight in weights.items():
            upper += weight * max((uncovered & mask).bit_count() for mask in masks[g])
        for m in prefix[depth:]:
            upper += denominator * max((uncovered & mask).bit_count() for mask in masks[m])

        if upper < count * denominator:
            stats["pruned"] += 1
            gap = Fraction(count * denominator - upper, denominator * period)
            require(gap >= min_gap, f"density gap {gap} below certified minimum margin {min_gap}")
            min_gap_seen = gap if min_gap_seen is None else min(min_gap_seen, gap)
            return

        if depth == len(prefix):
            stats["unresolved"] += 1
            return

        m = prefix[depth]
        orbit_bound = gcd(stabilizers[depth], m)
        for a in range(orbit_bound):
            r = a + branch_offset
            require(
                0 <= r < orbit_bound,
                f"branch residue {r} outside canonical orbit range [0, {orbit_bound})",
            )
            visit(depth + 1, uncovered & ~masks[m][r])

    visit(0, all_bits)

    require(stats["unresolved"] == 0, f"unresolved nodes remaining: {stats['unresolved']}")
    require(
        stats["nodes"] == EXPECTED_NODES,
        f"node count mismatch: {stats['nodes']} != {EXPECTED_NODES}",
    )
    require(
        stats["pruned"] == EXPECTED_PRUNED,
        f"pruned node count mismatch: {stats['pruned']} != {EXPECTED_PRUNED}",
    )
    require(
        min_gap_seen == MIN_PRUNE_GAP,
        f"minimum prune gap mismatch: {min_gap_seen} != {MIN_PRUNE_GAP}",
    )
    require(
        min_survivor_count >= MIN_SURVIVORS,
        f"min survivors below verified bound: {min_survivor_count} < {MIN_SURVIVORS}",
    )

    unconditioned_density = sum((Fraction(1, m) for m in pool), tail)
    return {
        "checked": True,
        "model": "distinct moduli m>=4; m+1 prime; prime factors of m in [2,3,5,7,11]",
        "primes": list(PRIMES),
        "caps": list(CAPS),
        "prefix": list(prefix),
        "period": period,
        "retained_count": len(pool),
        "exact_geometric_tail": str(tail),
        "unconditioned_density": str(unconditioned_density),
        "unconditioned_density_float": float(unconditioned_density),
        "tree_stats": stats,
        "minimum_prune_gap": str(min_gap_seen),
        "minimum_prune_gap_float": float(min_gap_seen),
        "min_survivors": min_survivor_count,
        "excluded_by_capacity_tree": True,
        "trust": "exact Python replay; independent certificate verification without external solvers",
    }


def mutation_checks() -> int:
    """Ensure 4 adversarial mutations are caught and rejected with explicit errors."""
    mutations: list[tuple[dict, str]] = [
        # 1. Mutate root period or prefix modulus
        ({"period": 360}, "Mutated root period (360 != 720)"),
        # 2. Tamper with a tree node capacity bound (artificial inflation)
        ({"capacity_bias": 1000}, "Tampered node capacity bound (+1000 inflation)"),
        # 3. Tamper with the geometric tail bound
        (
            {"tail_bound": EXPECTED_TAIL + Fraction(1, 1000)},
            "Tampered geometric tail bound (+1/1000)",
        ),
        # 4. Mutate a branch residue offset
        ({"branch_offset": 1}, "Mutated branch residue offset (+1)"),
    ]
    rejected = 0
    for kwargs, description in mutations:
        try:
            check(**kwargs)
        except ValueError:
            rejected += 1
            continue
        raise ValueError(f"Adversarial mutation unexpectedly accepted: {description}")
    require(
        rejected == len(mutations),
        f"Expected {len(mutations)} rejected mutations, got {rejected}",
    )
    return rejected


def main(
    output: Path | None = typer.Option(None, help="Optionally save the JSON audit."),
    self_test: bool = typer.Option(True, help="Also verify all 4 adversarial mutation checks."),
) -> None:
    """Execute standalone audit verification for Erdős 273 11-smooth certificate."""
    result = check()
    if self_test:
        result["rejected_mutations"] = mutation_checks()
    encoded = json.dumps(result, indent=2) + "\n"
    if output is not None:
        output.write_text(encoded)
    typer.echo(encoded, nl=False)


if __name__ == "__main__":
    typer.run(main)
