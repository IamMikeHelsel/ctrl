"""Independent linear-scan replay of the pinned native jerk branch choices."""

import gzip
import hashlib
import json
from bisect import bisect_right
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
S = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
HEADER = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/robot-motion/latency-noise-05/builder/.cache/ruckig-99751e6ebc7c963bb80e99fbbe66f2c279d1db57/include/ruckig/trajectory.hpp"
)
exports = json.loads((S / "ruckig-primary-exports.json").read_text())
schedules = json.loads((S / "reference-schedules.json").read_text())["schedules"]
root = json.loads((P / "pm_native_branch.json").read_text())
found = []
n = 0
for name, plans in exports.items():
    sched = next(x for x in schedules if x["case"] + "__" + x["method"] == name)
    starts = [F(x["start_exact"]) for x in sched["pieces"]]
    queries = json.loads(
        gzip.decompress((S / "native-checks" / (name + "-output.json.gz")).read_bytes())
    )["queries"]
    for query in queries:
        t = query["time"]
        selected = next((p for p in reversed(plans) if p["native_commit_float"] <= t), None)
        j = 0.0
        kind = "initial"
        local = None
        if selected is not None:
            p = selected["plan"]
            local = t - selected["native_commit_float"]
            if local >= p["duration"]:
                kind = "tail_duration"
            elif local < p["brake_duration"]:
                b = {x["index"]: x for x in p["phases"] if x["kind"] == "brake" and "index" in x}
                k = 0 if local < b[0]["duration"] else 1
                j = b[k]["jerk"]
                kind = f"brake_{k}"
            else:
                h = local - p["brake_duration"] if p["brake_duration"] > 0 else local
                hit = next(
                    (x for x in p["phases"] if x["kind"] == "main" and h < x["native_t_sum"]), None
                )
                if hit is None:
                    kind = "tail_main"
                else:
                    j = hit["jerk"]
                    kind = f"main_{hit['index']}"
        assert j == query["jerk"]
        n += 1
        piece = sched["pieces"][bisect_right(starts, F(t)) - 1]
        if piece["jerk"] != j:
            err = F(local) - (F(t) - F(selected["native_commit_float"]))
            remaining = F(piece["end_exact"]) - F(t)
            row = {
                "identity": name,
                "query_exact": str(F(t)),
                "native_selected": kind,
                "physical_selected": piece["origin"],
                "native_j": str(F(j)),
                "physical_j": str(F(piece["jerk"])),
                "local_subtraction_error": str(err),
                "physical_phase_end_minus_query": str(remaining),
                "local_binary": str(F(local)),
            }
            found.append(row)
            if name.startswith("persistent_goal"):
                assert err == remaining == F(1, 2**55)
            else:
                assert err == 0 and remaining == F(1, 2**53)
                assert F(p["tail"]["start"]) - F(p["duration"]) == F(1, 2**53)
assert n == 84316 and found == root["different_physical_branch"]
(P / "critic_branch.json").write_text(
    json.dumps(
        {
            "queries": n,
            "six_diagnoses": found,
            "source_header_sha256": hashlib.sha256(HEADER.read_bytes()).hexdigest(),
            "scope": "Independent Python binary64 branch replay after reading pinned native header; no fresh native run or formal floating-point proof.",
        },
        indent=2,
    )
    + "\n"
)
print(
    "All84316 jerk branches match; five query subtraction and one tail-duration diagnosis independently verified"
)
