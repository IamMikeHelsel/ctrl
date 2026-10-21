"""Independent frozen-data clock and sided-jet audit; rationalizes exported binary coefficients."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

P = Path(__file__).parent
S = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
fields = ["p", "v", "a", "jerk", "snap"]


def jet(piece, t):
    d = list(map(F, [piece[k] for k in fields]))
    h = t - F(piece["start_exact"])
    return [sum(d[j] * h ** (j - i) / factorial(j - i) for j in range(i, 5)) for i in range(5)]


def command(j):
    return 800 * j[0] + 60 * j[1] + F(3, 2) * j[2] + j[3] / 96


schedules = json.loads((S / "reference-schedules.json").read_text())["schedules"]
collisions = []
grouped = []
for s in schedules:
    if not s["method"].startswith("ruckig"):
        continue
    pieces = s["pieces"]
    atoms = {}
    count = 0
    for i, p in enumerate(pieces):
        a, b = F(p["start_exact"]), F(p["end_exact"])
        assert a < b
        if i:
            assert F(pieces[i - 1]["end_exact"]) == a
            jump = command(jet(p, a)) - command(jet(pieces[i - 1], a))
            atoms.setdefault(float(a), []).append((a, jump))
        if float(a) == float(b):
            assert i > 0 and i + 1 < len(pieces)
            left = command(jet(p, a)) - command(jet(pieces[i - 1], a))
            right = command(jet(pieces[i + 1], b)) - command(jet(p, b))
            collisions.append(
                {
                    "case": s["case"],
                    "method": s["method"],
                    "origin": p["origin"],
                    "start": str(a),
                    "end": str(b),
                    "width": str(b - a),
                    "float_time": float(a),
                    "left_jump": str(left),
                    "right_jump": str(right),
                    "two_jump_variation": str(abs(left) + abs(right)),
                    "signed_merge_variation": str(abs(left + right)),
                }
            )
    raw = sum(abs(v) for vs in atoms.values() for _, v in vs)
    merged = sum(abs(sum(v for _, v in vs)) for vs in atoms.values())
    assert merged <= raw
    grouped.append(
        {
            "case": s["case"],
            "method": s["method"],
            "jump_tv": str(raw),
            "merged_float_bucket_tv": str(merged),
            "lost_jump_tv": str(raw - merged),
        }
    )
assert len(collisions) == 9
w = next(x for x in collisions if x["case"] == "hold_jitter" and x["origin"] == "plan_29_main_0")
assert F(w["two_jump_variation"]) > F(3, 10) and F(w["signed_merge_variation"]) < F(1, 10**12)
# Positive local duration but equal native cumulative endpoints is a different, metadata-only case.
meta = json.loads((S / "clock-and-duration-audit.json").read_text())[
    "collapsed_positive_local_phases"
]
assert len(meta) == 1
m = meta[0]
assert F(m["phase"]["duration"]) == F(1, 2**58)
assert m["phase"]["start"] == m["phase"]["end"] and not m["before_next_commit_or_horizon"]
exports = json.loads((S / "ruckig-primary-exports.json").read_text())
plan = next(p for p in exports[m["stream_method"]] if p["commit_rational"] == m["commit"])
phase = next(p for p in plan["plan"]["phases"] if p["kind"] == "main" and p["index"] == 6)
assert phase["start"] == phase["end"] and F(phase["duration"]) > 0
absolute = F(plan["native_commit_exact"]) + F(phase["start"])
assert absolute > F(plan["executed_until_rational"])
subtractions = 0
for history in exports.values():
    for old, new in zip(history[:-1], history[1:], strict=True):
        a, b = new["native_commit_float"], old["native_commit_float"]
        assert F(a - b) == F(a) - F(b)
        assert F(b) / 2 <= F(a) <= 2 * F(b)
        subtractions += 1
assert subtractions == 480
assert F(1.0 - 0.1) != F(1.0) - F(0.1)
offsets = [
    abs(F(p["native_commit_exact"]) - F(p["commit_rational"]))
    for ps in exports.values()
    for p in ps
]
assert max(offsets) == F(3, 28147497671065600)
# Literal 05-to06 deltas are source records; no old failure retroactively changed.
result = {
    "executed_absolute_float_collisions": collisions,
    "grouping_losses": grouped,
    "metadata_only_collapsed_phase": m,
    "independently_checked_superseded_phase_absolute": str(absolute),
    "execution_stop": plan["executed_until_rational"],
    "max_scheduler_offset": str(max(offsets)),
    "exact_native_replacement_subtractions": subtractions,
    "wider_ratio_subtraction_negative": str(F(1.0 - 0.1) - (F(1.0) - F(0.1))),
    "scope": "Exact arithmetic on exported binary-polynomial interpretation. Grouping distinct exact execution times by binary64 changes the jump measure. This does not replay native C++ or certify continuous plant TV.",
}
(P / "critic_clocks.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    {
        "executed_collisions": len(collisions),
        "worst_grouping_loss": max(float(F(x["lost_jump_tv"])) for x in grouped),
        "metadata_only_duration": str(F(m["phase"]["duration"])),
    }
)
