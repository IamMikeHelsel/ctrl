"""Exact binary-coefficient audit of tiny executed native phases, never regenerates plans."""

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

SOURCE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder/reference-schedules.json"
)
WEIGHTS = [F(800), F(60), F(3, 2), F(1, 96)]


def jet(piece, time):
    t = time - F(piece["start_exact"])
    p, v, a, j, s = [F(piece[k]) for k in ["p", "v", "a", "jerk", "snap"]]
    return [
        p + v * t + a * t * t / 2 + j * t**3 / 6 + s * t**4 / 24,
        v + a * t + j * t * t / 2 + s * t**3 / 6,
        a + j * t + s * t * t / 2,
        j + s * t,
    ]


def command_jump(left, right):
    return sum(w * (y - x) for w, x, y in zip(WEIGHTS, left, right, strict=True))


saved = json.loads(SOURCE.read_text())
rows = []
for schedule in saved["schedules"]:
    if not schedule["method"].startswith("ruckig"):
        continue
    pieces = schedule["pieces"]
    for i in range(1, len(pieces) - 1):
        previous, p, after = pieces[i - 1 : i + 2]
        lo, hi = F(p["start_exact"]), F(p["end_exact"])
        dt = hi - lo
        assert dt > 0
        if dt > F(1, 10**9):
            continue
        assert F(previous["end_exact"]) == lo and F(after["start_exact"]) == hi
        jl = command_jump(jet(previous, lo), jet(p, lo))
        jr = command_jump(jet(p, hi), jet(after, hi))
        tv = abs(jl) + abs(jr)
        collapsed = abs(jl + jr)
        assert tv >= collapsed
        rows.append(
            {
                "case": schedule["case"],
                "method": schedule["method"],
                "piece_index": i,
                "origin": p["origin"],
                "start": lo,
                "end": hi,
                "width": dt,
                "absolute_float_endpoints_equal": float(lo) == float(hi),
                "left_command_jump": jl,
                "right_command_jump": jr,
                "two_jump_TV": tv,
                "net_atom_TV": collapsed,
                "lost_jump_TV": tv - collapsed,
                "left_jerk_jump": jet(p, lo)[3] - jet(previous, lo)[3],
                "right_jerk_jump": jet(after, hi)[3] - jet(p, hi)[3],
                "reference_delta_over_piece": [
                    y - x for x, y in zip(jet(p, lo), jet(p, hi), strict=True)
                ],
            }
        )
assert rows
best = max(
    (r for r in rows if r["absolute_float_endpoints_equal"]), key=lambda r: r["lost_jump_TV"]
)
assert best["lost_jump_TV"] > F(3, 10)
# Declared pulse diagnostic, source controller's jerk feedforward coefficient retained.
# j=J on [0,eps), otherwise0; polynomial q,v,a integrated without resets.
pulses = []
for eps in [F(1, 10**3), F(1, 10**9), F(1, 2**60)]:
    j = F(15, 2)
    jet_end = [j * eps**3 / 6, j * eps**2 / 2, j * eps, F(0)]
    tv_jumps = 2 * j / 96
    assert tv_jumps == F(5, 32)
    pulses.append(
        {
            "width": eps,
            "jerk": j,
            "retained_endpoint_jet": jet_end,
            "two_feedforward_jump_TV": tv_jumps,
            "direct_zero_duration_metadata_TV": 0,
        }
    )
output = {
    "source": str(SOURCE),
    "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "interpretation": "Exact rational interpretation of saved binary64 coefficients and exact schedule cuts; not bit-identical native evaluation.",
    "tiny_executed_count": len(rows),
    "collapsed_float_count": sum(r["absolute_float_endpoints_equal"] for r in rows),
    "strongest": best,
    "rows": rows,
    "pulse_diagnostics": pulses,
    "scope": "Jump-only ledger; continuous variation still separately required. No physical state reset or physical-TV simulation.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(output, default=str, indent=2) + "\n")
print(
    {
        "tiny_executed_count": len(rows),
        "collapsed_float_count": output["collapsed_float_count"],
        "best": {
            k: (float(best[k]) if isinstance(best[k], F) else best[k])
            for k in ["case", "method", "origin", "width", "two_jump_TV", "lost_jump_TV"]
        },
    }
)
