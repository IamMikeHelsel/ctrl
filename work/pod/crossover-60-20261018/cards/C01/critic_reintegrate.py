"""Independent physical-coordinate DOP853 replay of the fixed retuning screen."""

import csv
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

BASE = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)
phases = json.loads(SOURCE.read_text())
cases = json.loads((BASE / "domain_retuned_results.json").read_text())["cases"]
cases += json.loads((BASE / "domain_codesign_results.json").read_text())["cases"]


def derivatives(p):
    out = [list(map(float, map(F, p)))]
    for _ in range(4):
        out.append([i * c for i, c in enumerate(out[-1])][1:] or [0.0])
    return out


def horner(p, t):
    value = 0.0
    for c in reversed(p):
        value = value * t + c
    return value


out = []
for case in cases:
    direct = case["name"] == "direct"
    kp, kd, ka, ff = [float(F(case[key])) for key in ["kp", "kd", "ka", "k"]]
    snap_gain = float(F(case.get("snap_gain", "0")))
    state = np.zeros(3 if direct else 4)
    saved = list(csv.DictReader((BASE / ("domain_retuned_" + case["name"] + ".csv")).open()))
    differences = {key: 0.0 for key in ["x", "ex", "ev", "ea", "u", "actual_jerk"]}
    extrema = {"error": 0.0, "jerk": 0.0}
    count = 0
    for phase in phases:
        start, end = float(F(phase["start"])), float(F(phase["end"]))
        polys = derivatives(phase["position_coefficients_local_time"])

        def ref(time, start=start, polys=polys):
            return [horner(p, time - start) for p in polys]

        def outputs(
            time, z, ref=ref, kp=kp, kd=kd, ka=ka, ff=ff, direct=direct, snap_gain=snap_gain
        ):
            q, qv, qa, j, snap = ref(time)
            x, vel, acc = z[:3]
            ex, ev, ea = x - q, vel - qv, acc - qa
            target = qa - kp * ex - kd * ev - ka * ea + ff * j + snap_gain * snap
            u = target if direct else z[3]
            jerk = 80 * (u + 0.01 - acc)
            return ex, ev, ea, target, u, jerk

        def rhs(time, z, outputs=outputs, direct=direct):
            _, _, _, target, u, jerk = outputs(time, z)
            return [z[1], z[2], jerk] if direct else [z[1], z[2], jerk, 20 * (target - u)]

        sol = solve_ivp(
            rhs,
            (start, end),
            state,
            method="DOP853",
            rtol=1e-11,
            atol=1e-13,
            max_step=0.001,
            dense_output=True,
        )
        if not sol.success:
            raise ValueError(sol.message)
        for row in [r for r in saved if r["phase"] == phase["name"]]:
            t = float(F(row["t"]))
            z = sol.sol(t)
            ex, ev, ea, _, u, jerk = outputs(t, z)
            actual = dict(x=z[0], ex=ex, ev=ev, ea=ea, u=u, actual_jerk=jerk)
            for key, value in actual.items():
                differences[key] = max(differences[key], abs(value - float(row[key])))
            extrema["error"] = max(extrema["error"], abs(ex))
            extrema["jerk"] = max(extrema["jerk"], abs(jerk))
            count += 1
        state = sol.y[:, -1]
    if max(differences.values()) > 2e-9:
        raise ValueError("independent propagation mismatch " + str(differences))
    out.append(
        {
            "law": case["name"],
            "rows_compared": count,
            "maximum_differences": differences,
            "sampled_extrema": extrema,
            "scope": "independent numerical integration; no interval safety proof",
        }
    )
result = {
    "reference_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "integration": "physical x,v,a,u; DOP853 phase integration; retained states",
    "cases": out,
}
(BASE / "critic_reintegration_results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(out, indent=2))
