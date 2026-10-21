"""Audit actual output forms, beyond zero scalar-pairing rows; imports PM assembly explicitly."""

import json
from pathlib import Path

import pm_symbol as p

out = []
nonzero = []
index = 0
for group in ("L1", "L3", "Y2", "Y4p"):
    for local, x in enumerate(p.B[group]):
        forms = p.symbol(p.inject(group, x, [1] * 10), [1] * 10)
        if all(not y for y in forms):
            out.append(
                {
                    "index": index,
                    "group": group,
                    "local": local,
                    "basis": [[str(k), str(v)] for k, v in x.items()],
                }
            )
        else:
            nonzero.append(index)
        index += 1
assert len(out) == 35
assert all(x["group"] == "L3" for x in out)
assert all(1 not in next(iter(p.B["L3"][x["local"]])) for x in out)
result = {
    "zero_forms": out,
    "count": len(out),
    "description": "Exactly the 35 L3 basis triples not containing covector direction 1 have all four actual projected outputs zero for A.6.",
    "scope": "Uses shared domain exterior API and PM symbol assembly; verifies actual forms, not independently reconstructed projection code.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(result["description"])
