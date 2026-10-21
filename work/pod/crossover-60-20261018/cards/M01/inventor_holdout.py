"""Fixed prime197 tested on a separate short elliptic-operation batch."""

import json
from itertools import combinations
from pathlib import Path

from inventor_elliptic import A, add, encode, known, lift, records

# Fixed after the discovery batch and BEFORE these operations are evaluated.
PRIME = 197
squares = {z * z % PRIME for z in range(PRIME)}
seen = {r["point"][0] for r in records if "point" in r}
operations = [(f"3P{i + 1}", add(add(p, p), p)) for i, p in enumerate(known)]
operations += [
    (f"P{i + 1}+P{j + 1}+P{k + 1}", add(add(known[i], known[j]), known[k]))
    for i, j, k in combinations(range(4), 3)
]
output = []
for name, point in operations:
    if point is None or point[0] in seen:
        continue
    seen.add(point[0])
    entry = lift(point)
    x = point[0]
    violations = []
    for i, value in enumerate([x] + [x + a for a in A]):
        if value.denominator % PRIME:
            r = value.numerator * pow(value.denominator, -1, PRIME) % PRIME
            if r not in squares:
                violations.append([i, r])
    entry["operation"] = name
    entry["prime197_violations"] = violations
    output.append(entry)
summary = {
    "predeclared_prime": PRIME,
    "proposed_operations": len(operations),
    "new_finite_X_after_discovery_batch_deduplication": len(output),
    "rejected_by_fixed_prime197": sum(bool(r["prime197_violations"]) for r in output),
    "passed_prime197_but_failed_complete_lift": sum(
        not r["prime197_violations"] and not r["new_column"] for r in output
    ),
    "new_complete_columns": sum(r["new_column"] for r in output),
}
assert not any(r["new_column"] for r in output)
result = {
    "summary": summary,
    "records": output,
    "scope": "Second finite group-law batch validates or falsifies a posthoc-selected sieve on newX values. No denominator search, complete group search, or global obstruction claim.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(encode(result), indent=2) + "\n")
print(json.dumps(summary, indent=2))
