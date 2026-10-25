"""Independent exact replay of the seven-smooth conditional-capacity certificate.

AI-assisted research by the program manager subagent, 2026-10-18. This checker
uses plain residue lists, no search implementation imports, and no bit masks.
Python verification is evidence, not a Lean proof of the infinite-family claim.
Run with: uv run python work/273/check_seven.py [--output PATH] [--self-test]
"""

import json
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path

import typer

PRIMES = (2, 3, 5, 7)
CAPS = (10, 6, 4, 3)
PREFIX = (4, 6, 10, 12)
PERIOD = 60
MASS_BOUNDS = {4: 120, 6: 101, 10: 21, 12: 85, 20: 47, 30: 56, 60: 40}
SCALE = 1000
TAIL_BOUND = 5
MIN_GAP = 342


def require(condition: bool, message: str) -> None:
    """Keep verification active even under Python's optimized execution mode."""
    if not condition:
        raise ValueError(message)


def check(mass_bounds: dict[int, int], min_gap: int) -> dict:
    """Replay the fixed model, accepting only conservative certificate bounds."""
    require(set(mass_bounds) == set(MASS_BOUNDS), "unexpected gcd groups")
    require(all(v >= 0 for v in mass_bounds.values()), "negative mass bound")
    require(min_gap > 0, "claimed margin must be positive")
    sieve_primes = [n for n in range(3, 98) if all(n % d for d in range(2, isqrt(n) + 1))]
    pool = []
    for a, b, c, d in product(
        range(1, CAPS[0] + 1),
        range(CAPS[1] + 1),
        range(CAPS[2] + 1),
        range(CAPS[3] + 1),
    ):
        m = 2**a * 3**b * 5**c * 7**d
        # A prime m+1 passes: any prime divisor q of it must equal m+1.
        # Surviving composites only increase the resulting upper bound.
        if m >= 4 and all((m + 1) % q != 0 or m + 1 == q for q in sieve_primes):
            pool.append(m)
    require(len(pool) == len(set(pool)), "duplicate modulus in exponent box")
    require(set(PREFIX) <= set(pool), "prefix not present in admissible over-pool")
    masses: dict[int, Fraction] = {}
    for m in pool:
        if m not in PREFIX:
            g = gcd(m, PERIOD)
            masses[g] = masses.get(g, Fraction()) + Fraction(1, m)
    require(set(masses) == set(mass_bounds), "actual gcd groups differ")
    for g, mass in masses.items():
        require(mass <= Fraction(mass_bounds[g], SCALE), f"mass bound too small for gcd {g}")

    total = prod(Fraction(p, p - 1) for p in PRIMES[1:])
    box = (1 - Fraction(1, 2 ** CAPS[0])) * prod(
        Fraction(p, p - 1) * (1 - Fraction(1, p ** (cap + 1)))
        for p, cap in zip(PRIMES[1:], CAPS[1:], strict=True)
    )
    tail = total - box
    require(0 <= tail <= Fraction(TAIL_BOUND, SCALE), "geometric tail bound failed")

    worst_gap = None
    worst_coarsened_gap = None
    worst_residues = None
    assignments = 0
    for b, c, d in product(range(6), range(10), range(12)):
        residues = (0, b, c, d)
        # Translation fixes the first residue at zero without losing any case.
        uncovered = [
            r
            for r in range(PERIOD)
            if all(r % m != a for m, a in zip(PREFIX, residues, strict=True))
        ]
        capacity = PERIOD * TAIL_BOUND
        coarsened_capacity = PERIOD * TAIL_BOUND
        for g, weight in mass_bounds.items():
            largest_class = max(sum(r % g == a for r in uncovered) for a in range(g))
            capacity += weight * g * largest_class
            # The Lean core can replace the last three fiber maxima by 60/g.
            coarsened_count = PERIOD // g if g in (20, 30, 60) else largest_class
            require(largest_class <= coarsened_count, "invalid universal fiber bound")
            coarsened_capacity += weight * g * coarsened_count
        gap = SCALE * len(uncovered) - capacity
        coarsened_gap = SCALE * len(uncovered) - coarsened_capacity
        require(gap >= min_gap, f"claimed margin fails for residues {residues}: {gap}")
        require(coarsened_gap >= min_gap, f"coarsened margin fails for residues {residues}")
        if worst_coarsened_gap is None or coarsened_gap < worst_coarsened_gap:
            worst_coarsened_gap = coarsened_gap
        assignments += 1
        if worst_gap is None or gap < worst_gap:
            worst_gap, worst_residues = gap, residues
    require(assignments == 720, "prefix enumeration incomplete")
    return {
        "checked": True,
        "model": "distinct moduli m>=4; m+1 prime; prime factors of m in [2,3,5,7]",
        "primes": PRIMES,
        "caps": CAPS,
        "prefix": PREFIX,
        "period": PERIOD,
        "sieve_primes": sieve_primes,
        "retained_count": len(pool),
        "exact_group_masses": {str(g): str(masses[g]) for g in sorted(masses)},
        "mass_upper_bounds": {str(g): str(Fraction(v, SCALE)) for g, v in mass_bounds.items()},
        "exact_geometric_tail": str(tail),
        "tail_upper_bound": str(Fraction(TAIL_BOUND, SCALE)),
        "checked_assignments": assignments,
        "minimum_scaled_gap": worst_gap,
        "minimum_coarsened_scaled_gap": worst_coarsened_gap,
        "density_denominator": SCALE * PERIOD,
        "minimum_density_margin": str(Fraction(worst_gap, SCALE * PERIOD)),
        "worst_residues": worst_residues,
        "trust": "exact Python replay; full CRT and infinite-family Lean bridge not certified here",
        "ai_disclosure": "OpenAI Codex program manager subagent wrote this independent checker",
    }


def mutation_checks() -> int:
    """Ensure corrupted numerical claims are rejected rather than merely printed."""
    corruptions = [
        ({**MASS_BOUNDS, 12: 0}, MIN_GAP),
        (MASS_BOUNDS, MIN_GAP + 1),
        ({**MASS_BOUNDS, 4: -1}, MIN_GAP),
        ({g: v for g, v in MASS_BOUNDS.items() if g != 60}, MIN_GAP),
    ]
    for bounds, gap in corruptions:
        try:
            check(bounds, gap)
        except ValueError:
            continue
        raise ValueError("corrupted certificate unexpectedly accepted")
    return len(corruptions)


def main(
    output: Path | None = typer.Option(None, help="Optionally save the JSON audit."),
    self_test: bool = typer.Option(False, help="Also reject four corrupted certificates."),
) -> None:
    result = check(MASS_BOUNDS, MIN_GAP)
    if self_test:
        result["rejected_mutations"] = mutation_checks()
    encoded = json.dumps(result, indent=2) + "\n"
    if output is not None:
        output.write_text(encoded)
    typer.echo(encoded, nl=False)


if __name__ == "__main__":
    typer.run(main)
