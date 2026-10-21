"""Independent finite audit of the source period720 stabilizer reduction.
The separate Lean lemma proves the canonical-residue existence for arbitrary integers.
"""

import json
from math import gcd, lcm
from pathlib import Path

prefix = (4, 6, 10, 12, 16, 18, 30, 36)
period = lcm(*prefix)
stabilizer = 1
rows = []
checks = 0
for depth, modulus in enumerate(prefix):
    g = gcd(stabilizer, modulus)
    witnesses = []
    for a in range(modulus):
        b = a % g
        k = next(k for k in range(modulus // g) if (a + stabilizer * k) % modulus == b)
        shift = stabilizer * k
        assert (a + shift) % modulus == b
        assert all(shift % previous == 0 for previous in prefix[:depth])
        for x in range(period):
            assert (x % modulus == a) == ((x + shift) % modulus == b)
            assert all(x % previous == (x + shift) % previous for previous in prefix[:depth])
            checks += 1
        witnesses.append({"residue": a, "canonical": b, "multiple": k})
    rows.append(
        {
            "depth": depth,
            "stabilizer": stabilizer,
            "modulus": modulus,
            "canonical_count": g,
            "witnesses": witnesses,
        }
    )
    stabilizer = lcm(stabilizer, modulus)

# Semantic negative control: retaining only residue0 at depth1 omits an entire parity orbit.
assert all((1 + 4 * k) % 6 != 0 for k in range(6))
output = {
    "period": period,
    "orbit_rows": rows,
    "pointwise_checks": checks,
    "negative_control": {
        "L": 4,
        "m": 6,
        "a": 1,
        "bad_representative": 0,
        "reachable_residues": sorted({(1 + 4 * k) % 6 for k in range(6)}),
        "omitted_orbit_detected": True,
    },
    "scope": "Finite pointwise replay; no claim of full covering theorem or tree checker refinement.",
}
Path(__file__).with_name("domain_orbits_results.json").write_text(
    json.dumps(output, indent=2) + "\n"
)
print("period", period, "pointwise checks", checks)
print("canonical counts", [row["canonical_count"] for row in rows])
print("negative omitted orbit", output["negative_control"])
