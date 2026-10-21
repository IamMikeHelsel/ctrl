"""Read-only native carry and exact-real interpretation of exported binary boundary jets."""

import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

SRC = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/research/pods/2026-10-17/robot-motion/native-execution-06/builder"
)
OUT = Path(__file__).parent
keys = ["p", "v", "a", "jerk", "snap"]


def jet(piece, t):
    h = F(t) - F(piece["start_exact"])
    p, v, a, j, s = [F(piece[k]) for k in keys]
    return [
        p + v * h + a * h * h / 2 + j * h**3 / 6 + s * h**4 / 24,
        v + a * h + j * h * h / 2 + s * h**3 / 6,
        a + j * h + s * h * h / 2,
        j + s * h,
        s,
    ]


carry = []
for path in sorted((SRC / "native-plans").glob("*-output.json")):
    plans = json.loads(path.read_text())["plans"]
    n = 0
    for previous, current in zip(plans, plans[1:], strict=False):
        dt = current["native_commit"] - previous["native_commit"]
        assert dt == previous["native_elapsed_to_next_commit_or_horizon"]
        samples = [s for s in previous["plan"]["samples"] if s["t"] == dt]
        assert len(samples) == 1
        assert [samples[0][k] for k in ["p", "v", "a"]] == current["current_state"]
        n += 1
    carry.append(
        {
            "file": path.name,
            "plans": len(plans),
            "exact_carried_native_jets": n,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        }
    )

rows = []
for schedule in json.loads((SRC / "reference-schedules.json").read_text())["schedules"]:
    if not schedule["method"].startswith("ruckig"):
        continue
    pieces = schedule["pieces"]
    jumps = []
    maxima = [F(0)] * 3
    for left, right in zip(pieces, pieces[1:], strict=False):
        t = F(right["start_exact"])
        assert F(left["end_exact"]) == t
        a = jet(left, t)
        b = jet(right, t)
        delta = [y - x for x, y in zip(a, b, strict=True)]
        command = 800 * delta[0] + 60 * delta[1] + F(3, 2) * delta[2] + delta[3] / 96
        maxima = [max(m, abs(d)) for m, d in zip(maxima, delta[:3], strict=True)]
        jumps.append(
            {
                "t": t,
                "left_origin": left["origin"],
                "right_origin": right["origin"],
                "delta_qva_jerk": delta[:4],
                "delta_command_fixed_state": command,
            }
        )
    # Bound command-jump mass error if one reports jerk jumps alone.
    jet_error_mass = sum(
        800 * abs(j["delta_qva_jerk"][0])
        + 60 * abs(j["delta_qva_jerk"][1])
        + F(3, 2) * abs(j["delta_qva_jerk"][2])
        for j in jumps
    )
    command_mass = sum(abs(j["delta_command_fixed_state"]) for j in jumps)
    jerk_mass = sum(abs(j["delta_qva_jerk"][3]) / 96 for j in jumps)
    assert abs(command_mass - jerk_mass) <= jet_error_mass
    rows.append(
        {
            "case": schedule["case"],
            "method": schedule["method"],
            "pieces": len(pieces),
            "qva_jump_mass_error_bound": jet_error_mass,
            "command_vs_jerk_mass_discrepancy": abs(command_mass - jerk_mass),
            "jet_join_maxima": maxima,
            "exact_command_jump_TV": sum(abs(j["delta_command_fixed_state"]) for j in jumps),
            "exact_jerk_jump_TV": sum(abs(j["delta_qva_jerk"][3]) for j in jumps),
            "nonzero_qva_join_count": sum(any(j["delta_qva_jerk"][:3]) for j in jumps),
            "jumps": jumps,
        }
    )
result = {
    "scope": "Native saved-double carry equality; exact-real polynomial interpretation of exported binary coefficients. Not fresh native runtime, bit-perfect polynomial evaluation, continuous fidelity theorem, or physical validation.",
    "native_histories": carry,
    "native_total_plans": sum(r["plans"] for r in carry),
    "native_total_carries": sum(r["exact_carried_native_jets"] for r in carry),
    "schedules": rows,
    "source_sha256": {
        n: hashlib.sha256((SRC / n).read_bytes()).hexdigest()
        for n in [
            "native_execution.cpp",
            "profile_export.hpp",
            "make_references.py",
            "run_comparison.py",
            "reference-schedules.json",
        ]
    },
}
(OUT / "domain_audit.json").write_text(json.dumps(result, default=str, indent=2) + "\n")
print("Native plans/carries", result["native_total_plans"], result["native_total_carries"])
for r in rows:
    print(
        r["case"],
        r["method"],
        "joins",
        r["nonzero_qva_join_count"],
        "max qva",
        list(map(float, r["jet_join_maxima"])),
        "jumpTV",
        float(r["exact_command_jump_TV"]),
    )
