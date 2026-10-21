"""Exact13-coordinate refinement at modulus52, all translation orbits, full tail."""

import json
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path("work/273/candidates/20261019-052643-273-solve-298c/probe-13-spark.json")


def main():
    saved = json.loads(SOURCE.read_text())
    primes, caps = saved["primes"], saved["caps"]
    old_period, new_modulus = saved["period"], 52
    period = lcm(old_period, new_modulus)
    prefix = {m for m, _ in saved["worst_assignment"]}
    assert lcm(*prefix) == old_period
    powers = [[2**a for a in range(1, caps[0] + 1)]] + [
        [p**a for a in range(c + 1)] for p, c in zip(primes[1:], caps[1:], strict=True)
    ]
    pool = []
    for factors in product(*powers):
        m = prod(factors)
        if m >= 4 and pow(2, m, m + 1) == pow(3, m, m + 1) == 1:
            pool.append(m)
    total = prod(F(p, p - 1) for p in primes[1:])
    box = (1 - F(1, 2 ** caps[0])) * prod(
        F(p, p - 1) * (1 - F(1, p ** (c + 1))) for p, c in zip(primes[1:], caps[1:], strict=True)
    )
    tail = total - box
    assert tail == F(saved["tail"]) and len(pool) == saved["retained_count"]
    assert new_modulus in pool and new_modulus not in prefix
    assert all((new_modulus + 1) % q for q in range(2, 8))  # 53 prime, sqrt53<8.
    masses = {}
    for m in pool:
        if m not in prefix:
            g = gcd(m, period)
            masses[g] = masses.get(g, F()) + F(1, m)
    denominator = lcm(tail.denominator, *(v.denominator for v in masses.values()))
    weights = {g: int(v * denominator) * g for g, v in masses.items()}
    old_survivors = [
        x for x in range(old_period) if all(x % m != a for m, a in saved["worst_assignment"])
    ]
    survivors = [x + k * old_period for k in range(period // old_period) for x in old_survivors]
    assert {(x + old_period) % period for x in survivors} == set(survivors)

    def capacity(values, remove52):
        counts = {g: max(Counter(x % g for x in values).values(), default=0) for g in masses}
        upper = int(tail * denominator) * period
        upper += sum(weights[g] * counts[g] for g in masses)
        if remove52:
            upper -= denominator * counts[new_modulus]
        return F(upper - len(values) * denominator, denominator * period), counts

    baseline, _ = capacity(survivors, False)
    assert baseline == F(saved["worst_unresolved_excess"])
    orbit_count = gcd(old_period, new_modulus)
    records = []
    for a in range(orbit_count):
        orbit = sorted({(a + k * old_period) % new_modulus for k in range(new_modulus)})
        assert len(orbit) == new_modulus // orbit_count
        child = [x for x in survivors if x % new_modulus != a]
        next_residue = (a + old_period) % new_modulus
        assert {(x + old_period) % period for x in child} == {
            x for x in survivors if x % new_modulus != next_residue
        }
        value, counts = capacity(child, True)
        records.append(
            {
                "representative": a,
                "full_residue_orbit": orbit,
                "survivor_count": len(child),
                "excess": str(value),
                "excess_float": float(value),
                "excluded": value < 0,
                "conditional_max_counts": {str(g): c for g, c in sorted(counts.items())},
            }
        )
    assert sorted(a for r in records for a in r["full_residue_orbit"]) == list(range(new_modulus))
    result = {
        "scope": "Saved13-smooth leaf refined only by52. All52 residues covered by4 translation orbits; exact unchanged infinite tail, no global tree.",
        "old_period": old_period,
        "new_period": period,
        "new_modulus": new_modulus,
        "tail": str(tail),
        "before_survivors": len(survivors),
        "baseline_excess": str(baseline),
        "period_lift_only_preserves_bound": True,
        "translation_preserves_parent_and_maps_children": True,
        "gcd_group_count": len(masses),
        "branches": records,
        "worst_excess": str(max(F(r["excess"]) for r in records)),
        "all_branches_excluded": all(r["excluded"] for r in records),
    }
    (HERE / "inventor_lift.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "branches"}, indent=2))
    print(
        json.dumps(
            [{k: v for k, v in r.items() if k != "conditional_max_counts"} for r in records],
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
