"""Independent saved native queries versus exact binary-coefficient polynomial interpretation."""

import gzip
import json
from bisect import bisect_right
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
S = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
schedules = json.loads((S / "reference-schedules.json").read_text())["schedules"]
rows = []
for s in schedules:
    if not s["method"].startswith("ruckig"):
        continue
    identity = s["case"] + "__" + s["method"]
    native = json.loads(
        gzip.decompress((S / "native-checks" / (identity + "-output.json.gz")).read_bytes())
    )
    starts = [F(p["start_exact"]) for p in s["pieces"]]
    coeff = [[F(p[k]) for k in ["p", "v", "a", "jerk", "snap"]] for p in s["pieces"]]
    maxerr = [F(0), F(0), F(0)]
    mismatch = []
    for sample in native["queries"]:
        t = F(sample["time"])
        i = bisect_right(starts, t) - 1
        h = t - starts[i]
        p, v, a, j, snap = coeff[i]
        q = p + h * (v + h * (a / 2 + h * (j / 6 + h * snap / 24)))
        qv = v + h * (a + h * (j / 2 + h * snap / 6))
        qa = a + h * (j + h * snap / 2)
        jj = j + h * snap
        for k, key in enumerate(["q", "qv", "qa"]):
            maxerr[k] = max(maxerr[k], abs(F(sample[key]) - [q, qv, qa][k]))
        if abs(F(sample["jerk"]) - jj) > F(1, 10**8):
            mismatch.append(
                {
                    "t": str(t),
                    "native_j": str(F(sample["jerk"])),
                    "polynomial_j": str(jj),
                    "piece_origin": s["pieces"][i]["origin"],
                }
            )
    assert all(
        e <= bound
        for e, bound in zip(maxerr, [F(1, 10**8), F(1, 10**8), F(1, 10**10)], strict=True)
    )
    rows.append(
        {
            "identity": identity,
            "queries": len(native["queries"]),
            "max_exact_rational_residual": list(map(str, maxerr)),
            "jerk_side_mismatches": mismatch,
        }
    )
assert sum(x["queries"] for x in rows) == 84316
assert sum(len(x["jerk_side_mismatches"]) for x in rows) == 6
(P / "critic_native.json").write_text(
    json.dumps(
        {
            "rows": rows,
            "queries": 84316,
            "mismatches": 6,
            "scope": "Read-only saved native oracle comparison. Independent rational interpretation, not fresh C++ run or exact binary-operation-order mimic. q/v/a tolerances pass; full jet identity does not.",
        },
        indent=2,
    )
    + "\n"
)
print(
    "84316 independent exact polynomial query checks pass q/v/a bounds; six jerk-side disagreements reproduced"
)
