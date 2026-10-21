"""Exact audit separating native subtraction rounding from scheduler rounding."""

import json
from fractions import Fraction as F
from pathlib import Path

src = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
rows = []
for file in sorted((src / "native-plans").glob("*-output.json")):
    plans = json.loads(file.read_text())["plans"]
    for i, (a, b) in enumerate(zip(plans, plans[1:], strict=False)):
        x = F(a["native_commit"])
        y = F(b["native_commit"])
        native = F(b["native_commit"] - a["native_commit"])
        exact = y - x
        rows.append(
            {
                "file": file.name,
                "replacement": i + 1,
                "previous_binary_commit": x,
                "next_binary_commit": y,
                "exact_binary_difference": exact,
                "native_difference": native,
                "rounding_error": native - exact,
                "sterbenz_sufficient_ratio": x > 0 and x / 2 <= y <= 2 * x,
            }
        )
assert len(rows) == 480
print(
    "all480 exact?",
    all(r["rounding_error"] == 0 for r in rows),
    "Sterbenz sufficient",
    sum(r["sterbenz_sufficient_ratio"] for r in rows),
)
print(
    "outside sufficient ratio",
    [
        (r["file"], r["replacement"], str(r["rounding_error"]))
        for r in rows
        if not r["sterbenz_sufficient_ratio"]
    ],
)
Path(__file__).with_suffix(".json").write_text(
    json.dumps(
        {
            "scope": "Saved binary doubles interpreted exactly. Sterbenz ratio is a sufficient condition only; actual subtraction equality independently checked per row. Not a claim for arbitrary commit schedules.",
            "rows": rows,
        },
        default=str,
        indent=2,
    )
    + "\n"
)
