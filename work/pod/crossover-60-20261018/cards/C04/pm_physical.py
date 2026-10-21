"""Numerical same-guard retained-state executions with genuinely older readings."""

import json
from fractions import Fraction as Q
from itertools import product
from math import exp
from pathlib import Path

HERE = Path(__file__).resolve().parent
weights = [Q(51, 50), Q(101, 100), Q(1)]
errors = [Q(101533, 10**8), Q(368033, 10**8), Q(1042283, 10**8)]
noise = [Q(1, 1000), Q(1, 100), Q(1, 20)]
D = 0.0005
age = 0.015
spacing = age - D
horizon = 2.0


def policy(m):
    offsets = [m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16]
    K = max(
        Q(9, 200),
        *(
            (offsets[i] - offsets[j] + errors[i] + errors[j]) / (weights[i] + weights[j])
            for i in range(3)
            for j in range(3)
        ),
    )
    c = max(offsets[i] + errors[i] - weights[i] * K for i in range(3))
    return float(c), float(K)


def flow(state, u, r, delta, dt):
    x, v, a = state
    target = u + delta
    e = exp(-r * dt)
    return (
        x + v * dt + target * dt * dt / 2 + (a - target) * (dt / r - (1 - e) / (r * r)),
        v + target * dt + (a - target) * (1 - e) / r,
        target + (a - target) * e,
    )


def command(c, m):
    return -(16 / 3) * (m[0] - c) - 6 * m[1] - m[2] / 2


records = []
for mv, ma, signs, mode in product(
    (Q(-561, 50000), Q(561, 50000)), (Q(-127, 100), Q(-1, 5)), product((-1, 1), repeat=3), range(2)
):
    m = (Q(143, 1000), mv, ma)
    c, K = policy(m)
    state = tuple(float(m[i] - signs[i] * noise[i]) for i in range(3))
    maxx = state[0]
    max_age = 0.0
    maxu = 0.0
    max_weight_violation = -1.0
    max_shrink_violation = -1.0
    t = 0.0
    u = -1.21
    r = 8 if mode == 0 else 12
    delta = 0.01 if mode == 0 else -0.01
    last_read = tuple(float(v) for v in m)
    stamp = 0.0
    index = 0
    while t < horizon - 1e-12:
        dispatch = D + index * spacing
        if index == 0:
            intervals = [(dispatch, "dispatch")]
        else:
            intervals = [(dispatch - D, "sample"), (dispatch, "dispatch")]
        for end, event in intervals:
            end = min(end, horizon)
            dt = end - t
            if dt < 0:
                continue
            for k in range(1, 21):
                tt = t + dt * k / 20
                ss = flow(state, u, r, delta, dt * k / 20)
                maxx = max(maxx, ss[0])
                z = (ss[0] - c, ss[0] - c + ss[1] / 4, ss[0] - c + ss[1] / 2 + ss[2] / 16)
                if tt >= D:
                    env = max(0.045, K - (3 / 1700) * (tt - D))
                    max_weight_violation = max(
                        max_weight_violation,
                        max(abs(z[i]) - float(weights[i]) * K for i in range(3)),
                    )
                    max_shrink_violation = max(
                        max_shrink_violation,
                        max(abs(z[i]) - float(weights[i]) * env for i in range(3)),
                    )
                    max_age = max(max_age, tt - stamp)
            state = flow(state, u, r, delta, dt)
            t = end
            if t >= horizon:
                break
            if event == "sample":
                pending = tuple(
                    state[i] + float(noise[i]) * ((-1) ** (index + i + mode)) for i in range(3)
                )
            else:
                if index > 0:
                    last_read = pending
                    stamp = dispatch - D
                raw = command(c, last_read)
                maxu = max(maxu, abs(raw))
                u = max(-2, min(2, raw))
                r = 8 if (index + mode) % 2 == 0 else 12
                delta = 0.01 * (-1) ** (index + mode)
        index += 1
    records.append(
        {
            "reading": [str(x) for x in m],
            "initial_sensor_signs": signs,
            "mode": mode,
            "center": c,
            "policy_radius": K,
            "peak_sampled_x": maxx,
            "max_information_age": max_age,
            "max_unclipped_command": maxu,
            "max_weighted_box_violation": max_weight_violation,
            "max_shrink_violation": max_shrink_violation,
            "final_state": state,
        }
    )
result = {
    "cases": records,
    "count": len(records),
    "max_x": max(x["peak_sampled_x"] for x in records),
    "max_age": max(x["max_information_age"] for x in records),
    "max_unclipped_command": max(x["max_unclipped_command"] for x in records),
    "max_box_violation": max(x["max_weighted_box_violation"] for x in records),
    "max_shrink_violation": max(x["max_shrink_violation"] for x in records),
    "scope": "Binary64 trajectory samples with analytic constant-target segment flow, not all-time enclosures or Leanexecution. All use original center/guard and continuous retained state; first stale reading persists through15ms.",
}
(HERE / "pm_physical.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "cases"}, indent=2))
