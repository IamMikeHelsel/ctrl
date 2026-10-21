"""Frozen-reference numerical comparison; isolated feedback retuning experiment.

Run via uv with the already installed scientific Python runtime:
uv run --no-project --python /usr/local/bin/python3 python <this file>
Sampled results are not continuous-time guarantees.
"""

import csv
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.linalg import expm

REFERENCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)
HERE = Path(__file__).resolve().parent
STEP = F(1, 2000)


def diff(p):
    return [i * p[i] for i in range(1, len(p))] or [F(0)]


def evaluate(p, t):
    out = 0.0
    for coefficient in reversed(p):
        out = out * t + float(coefficient)
    return out


def phases():
    out = []
    for phase in json.loads(REFERENCE.read_text()):
        polynomials = [list(map(F, phase["position_coefficients_local_time"]))]
        for _ in range(4):
            polynomials.append(diff(polynomials[-1]))
        out.append((F(phase["start"]), F(phase["end"]), phase["name"], polynomials))
    return out


def run(name, kp, kd, ka, k, direct=False, rate=80, disturbance=F(1, 100), snap_gain=F(0)):
    n = 3 if direct else 4
    state = np.zeros(n)
    rows = []
    for start, end, phase_name, polynomials in phases():
        a = np.zeros((n + 4, n + 4))
        a[0, 1] = a[1, 2] = 10
        if direct:
            a[2, :3] = [-rate * float(kp) / 100, -rate * float(kd) / 10, -rate * (1 + float(ka))]
        else:
            a[2, 2:4] = [-rate, rate]
            a[3, :4] = [-float(kp) / 5, -2 * float(kd), -20 * float(ka), -20]
        a[2, n] = rate * float(disturbance) / 100
        for index, coefficient in enumerate(polynomials[3]):
            a[2, n + index] += float(coefficient) * (float(rate * k - 1) / 100 if direct else -0.01)
            if not direct:
                a[3, n + index] = float((20 * k - 1) * coefficient / 100)
        if not direct:
            for index, coefficient in enumerate(polynomials[4]):
                a[3, n + index] += float(20 * snap_gain * coefficient / 100)
        for index in range(1, 4):
            a[n + index, n + index - 1] = index
        augmented = np.r_[state, 1.0, 0.0, 0.0, 0.0]
        times = sorted(
            {start, end}
            | {i * STEP for i in range(math.ceil(start / STEP), math.floor(end / STEP) + 1)}
        )
        cache = {}
        previous = start
        for t in times:
            delta = t - previous
            if delta:
                if delta not in cache:
                    cache[delta] = expm(a * float(delta))
                augmented = cache[delta] @ augmented
            q, qv, qa, j, snap = [evaluate(p, float(t - start)) for p in polynomials]
            e, ev, ea = augmented[0], 10 * augmented[1], 100 * augmented[2]
            target = (
                qa
                - float(kp) * e
                - float(kd) * ev
                - float(ka) * ea
                + float(k) * j
                + float(snap_gain) * snap
            )
            u = target if direct else qa + 100 * augmented[3]
            jerk = rate * (u + float(disturbance) - qa - ea)
            uprime = (
                (1 + float(ka)) * j
                - float(kp) * ev
                - float(kd) * ea
                - float(ka) * jerk
                + float(k) * snap
                if direct
                else 20 * (target - u)
            )
            rows.append(
                dict(
                    t=str(t),
                    phase=phase_name,
                    q=q,
                    x=q + e,
                    ex=e,
                    ev=ev,
                    ea=ea,
                    u=u,
                    actual_jerk=jerk,
                    uprime=uprime,
                )
            )
            previous = t
        state = augmented[:n].copy()
    with (HERE / f"domain_retuned_{name}.csv").open("w") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    result = {
        "name": name,
        "kp": str(kp),
        "kd": str(kd),
        "ka": str(ka),
        "k": str(k),
        "snap_gain": str(snap_gain),
        "rate": rate,
        "disturbance": str(disturbance),
        "samples": len(rows),
        "sampled_max_error_m": max(abs(row["ex"]) for row in rows),
        "sampled_peak_actual_jerk": max(abs(row["actual_jerk"]) for row in rows),
        "sampled_command_tv": sum(
            abs(a["u"] - b["u"]) for a, b in zip(rows, rows[1:], strict=False)
        ),
        "initial": rows[0],
        "final": rows[-1],
    }
    result["sampled_tracking_pass"] = bool(result["sampled_max_error_m"] <= 0.0002)
    return result


def main():
    cases = [
        run("direct", F(800), F(60), F(1, 2), F(1, 96), direct=True),
        run("old", F(800), F(60), F(1, 2), F(1, 96)),
        run("compensated", F(800), F(60), F(1, 2), F(29, 480)),
        run("pole20_20_20_40", F(200), F(35), F(5, 4), F(29, 480)),
        run("pole25_quadruple", F(15625, 64), F(625, 16), F(43, 32), F(29, 480)),
    ]
    out = {
        "status": "finite-grid numerical experiment; no all-time or hardware claim",
        "reference_path": str(REFERENCE),
        "reference_sha256": hashlib.sha256(REFERENCE.read_bytes()).hexdigest(),
        "step": str(STEP),
        "filter_rate": 20,
        "filter_initial_u": 0,
        "cases": cases,
    }
    (HERE / "domain_retuned_results.json").write_text(json.dumps(out, indent=2) + "\n")
    for result in cases:
        print(
            result["name"],
            "error_mm",
            result["sampled_max_error_m"] * 1000,
            "actual_jerk",
            result["sampled_peak_actual_jerk"],
            "command_tv",
            result["sampled_command_tv"],
        )


if __name__ == "__main__":
    main()
