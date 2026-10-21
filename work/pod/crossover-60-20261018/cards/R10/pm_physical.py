"""Independent scalar plant propagation; numerical sampled evidence only."""

import json
import math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import numpy as np
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parent


def reference(events, t):
    result = []
    for d in range(5):
        total = F(0)
        for tau, delta, h in events:
            for k in range(5):
                age = t - tau - k * h
                if age > 0 or (age == 0 and d == 4):
                    total += (
                        delta
                        * (-1) ** k
                        * math.comb(4, k)
                        * age ** (4 - d)
                        / (math.factorial(4 - d) * h**4)
                    )
        result.append(total)
    return result


@lru_cache(None)
def transition(rate, disturbance, dt):
    A = np.zeros((9, 9))
    A[0, 1] = 1
    A[1, 2] = 1
    A[2, :] = rate * np.array([-800, -60, -1.5, 800, 60, 1.5, 1 / 96, 0, disturbance])
    for i in range(3, 7):
        A[i, i + 1] = 1
    return expm(A * dt)


cases = {
    "return_widen_new_only": (
        [(F("0.22"), F(".02"), F(".2")), (F(".52"), F("-.02"), F(".25"))],
        F("1.7"),
        F(0),
        F(".52"),
    ),
    "predelivery_widen_new_only": (
        [(F(".22"), F(".02"), F(".2")), (F(".52"), F("-.02"), F(".25"))],
        F(".51"),
        F(0),
        F(".52"),
    ),
    "buffered_unchanged": (
        [(F(".28"), F(".02"), F(".2")), (F(".68"), F("-.02"), F(".2"))],
        F("1.9"),
        F(0),
        F(".68"),
    ),
    "far_widen_new_only": (
        [(F(".22"), F(".02"), F(".2")), (F(".52"), F("-.04"), F(".3"))],
        F("1.9"),
        F("-.02"),
        F(".52"),
    ),
    "frozen_return": (
        [(F(".22"), F(".02"), F(".2")), (F(".52"), F("-.02"), F(".2"))],
        F("1.7"),
        F(0),
        F(".52"),
    ),
    "frozen_far_rejected": ([(F(".22"), F(".02"), F(".2"))], F("1.9"), F("-.02"), F(".52")),
}
records = []
for name, (events, deadline, goal, execution) in cases.items():
    for denominator in [1000, 2000]:
        nodes = set(F(i, denominator) for i in range(int(F("2.5") * denominator) + 1))
        nodes |= {tau + k * h for tau, _, h in events for k in range(5)}
        nodes |= {deadline, F(".5"), execution}
        nodes = sorted(nodes)
        for rate in [80, 100, 120]:
            for disturbance in [0.0, 0.01]:
                x = np.zeros(3)
                endpoint = None
                progress = None
                last_bad = None
                samples = []
                peaks = np.zeros(4)
                for index, t in enumerate(nodes):
                    ref = np.array(list(map(float, reference(events, t))))
                    u = (
                        -800 * x[0]
                        - 60 * x[1]
                        - 0.5 * x[2]
                        + 800 * ref[0]
                        + 60 * ref[1]
                        + 1.5 * ref[2]
                        + ref[3] / 96
                    )
                    actual_jerk = rate * (u + disturbance - x[2])
                    peaks = np.maximum(peaks, np.abs([x[1], x[2], actual_jerk, x[0] - ref[0]]))
                    good = (
                        abs(x[0] - float(goal)) <= 0.0002
                        and abs(x[1]) <= 0.001
                        and abs(x[2]) <= 0.02
                    )
                    samples.append((float(t), good))
                    if not good:
                        last_bad = index
                    if t == deadline:
                        endpoint = x.copy()
                    if t == F(".5"):
                        progress = float(x[0])
                    if index + 1 < len(nodes):
                        dt = float(nodes[index + 1] - t)
                        augmented = np.array([*x, *ref, 1.0])
                        x = (transition(rate, disturbance, dt) @ augmented)[:3]
                settling = (
                    None
                    if last_bad == len(nodes) - 1
                    else samples[0 if last_bad is None else last_bad + 1][0]
                )
                passes = (
                    abs(endpoint[0] - float(goal)) <= 0.0002
                    and abs(endpoint[1]) <= 0.001
                    and abs(endpoint[2]) <= 0.02
                )
                remain = all(good for t, good in samples if t >= float(deadline))
                records.append(
                    {
                        "case": name,
                        "step": 1 / denominator,
                        "rate": rate,
                        "disturbance": disturbance,
                        "deadline": float(deadline),
                        "endpoint": endpoint.tolist(),
                        "goal_error": float(endpoint[0] - float(goal)),
                        "endpoint_pass": bool(passes),
                        "remain_sample_pass": remain,
                        "progress_at_half": progress,
                        "progress_pass": progress >= 0.001,
                        "causal_service_pass": deadline >= execution,
                        "settling_sample": settling,
                        "physical_peak_v_a_j_internalerror": peaks.tolist(),
                        "scope": "Original scalar plant/controller, independent numerical matrix exponential, no reset; sampled remain/peaks only, no all-time or hardware claim.",
                    }
                )
(ROOT / "pm_physical.json").write_text(
    json.dumps(
        {
            "records": records,
            "counts": len(records),
            "tool": "existing scipy matrix exponential; independent source reconstruction",
        },
        indent=2,
    )
    + "\n"
)
for name in cases:
    rows = [r for r in records if r["case"] == name and r["step"] == 0.0005]
    print(
        name,
        sum(
            r["endpoint_pass"]
            and r["remain_sample_pass"]
            and r["progress_pass"]
            and r["causal_service_pass"]
            for r in rows
        ),
        "/6",
        "max goalerr",
        max(abs(r["goal_error"]) for r in rows),
    )
