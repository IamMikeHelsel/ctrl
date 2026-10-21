"""Pinned native branch semantics replay, using saved profiles and binary64 add/subtract."""

import gzip
import json
from bisect import bisect_right
from fractions import Fraction as F
from pathlib import Path

S = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
exports = json.loads((S / "ruckig-primary-exports.json").read_text())
schedules = json.loads((S / "reference-schedules.json").read_text())["schedules"]
rows = []
count = 0
for name, plans in exports.items():
    native = json.loads(
        gzip.decompress((S / "native-checks" / f"{name}-output.json.gz").read_bytes())
    )
    commits = [p["native_commit_float"] for p in plans]
    schedule = next(s for s in schedules if s["case"] + "__" + s["method"] == name)
    cuts = [F(p["start_exact"]) for p in schedule["pieces"]]
    for sample in native["queries"]:
        t = sample["time"]
        idx = bisect_right(commits, t) - 1
        phase = "initial"
        jj = 0.0
        local = None
        if idx >= 0:
            p = plans[idx]["plan"]
            local = t - commits[idx]
            main = [x for x in p["phases"] if x["kind"] == "main"]
            if local >= p["duration"]:
                phase = "tail_duration"
            elif p["brake_duration"] > 0 and local < p["brake_duration"]:
                brake = {
                    x["index"]: x for x in p["phases"] if x["kind"] == "brake" and "index" in x
                }
                bi = 0 if local < brake[0]["duration"] else 1
                jj = brake[bi]["jerk"]
                phase = f"brake_{bi}"
            else:
                afterbrake = local - p["brake_duration"] if p["brake_duration"] > 0 else local
                if afterbrake >= main[-1]["native_t_sum"]:
                    phase = "tail_main"
                else:
                    pi = bisect_right([x["native_t_sum"] for x in main], afterbrake)
                    jj = main[pi]["jerk"]
                    phase = f"main_{pi}"
        assert jj == sample["jerk"], (name, t, phase, jj, sample["jerk"])
        count += 1
        physical = schedule["pieces"][bisect_right(cuts, F(t)) - 1]
        if physical["jerk"] != jj:
            exactlocal = F(t) - F(commits[idx])
            rows.append(
                {
                    "identity": name,
                    "query_exact": str(F(t)),
                    "native_selected": phase,
                    "physical_selected": physical["origin"],
                    "native_j": str(F(jj)),
                    "physical_j": str(F(physical["jerk"])),
                    "local_subtraction_error": str(F(local) - exactlocal),
                    "physical_phase_end_minus_query": str(F(physical["end_exact"]) - F(t)),
                    "local_binary": str(F(local)),
                }
            )
assert count == 84316 and len(rows) == 6
Path(__file__).with_suffix(".json").write_text(
    json.dumps(
        {
            "queries": count,
            "native_jerk_matches": count,
            "different_physical_branch": rows,
            "scope": "Read-only pinned comparison-branch replay in Python binary64, not C++ rebuild/full arithmetic proof. Saved profile authority and platform float semantics explicit.",
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(rows, indent=2))
