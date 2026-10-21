"""Matched finite-horizon coefficient tuning with pure-Python RK4; numerical only."""

import json
import math
from pathlib import Path

HERE = Path(__file__).parent
J, H, SIGMA, W = 10.0, 0.02, 1.0, 0.0005
TRAIN = ["fixed8", "fixed10", "fixed12", "phase0"]
TEST = ["phase1", "phase2", "phase3"]


def rate(t, name):
    if name.startswith("fixed"):
        return float(name[5:]) * SIGMA
    phase = int(name[5:]) * math.pi / 2
    return SIGMA * (10 - 2 * math.tanh(4 * math.cos(math.pi * t / (2 * H) + phase)))


def field(t, y, jerk, name):
    r = rate(t, name)
    disturbance = -W * (-math.expm1(-20 * t))
    b, v, a, z, zv, za = y
    return [
        v,
        a,
        r * (-8 * SIGMA**2 * b - 6 * SIGMA * v - 1.5 * a + disturbance) - jerk,
        zv,
        za,
        r * (-8 * SIGMA**2 * z - 6 * SIGMA * zv - 1.5 * za + jerk / SIGMA),
    ]


def trace(name, step):
    y = [0.0] * 6
    t0 = 0.0
    rows = [(0.0, 0.0, 0.0)]
    for duration, jerk in [(H, J), (H, -J), (H, -J), (H, J), (4.0, 0.0)]:
        n = math.ceil(duration / step)
        dt = duration / n
        for k in range(n):
            t = t0 + k * dt
            k1 = field(t, y, jerk, name)
            k2 = field(t + dt / 2, [v + dt * f / 2 for v, f in zip(y, k1, strict=True)], jerk, name)
            k3 = field(t + dt / 2, [v + dt * f / 2 for v, f in zip(y, k2, strict=True)], jerk, name)
            k4 = field(t + dt, [v + dt * f for v, f in zip(y, k3, strict=True)], jerk, name)
            y = [
                v + dt * (a + 2 * b + 2 * c + d) / 6
                for v, a, b, c, d in zip(y, k1, k2, k3, k4, strict=True)
            ]
            rows.append((t + dt, y[0], y[3]))
        t0 += duration
    return rows


def objective(d, lines):
    return max(abs(b + d * a) for _, _, b, a in lines)


def solve(lines):
    lo, hi = -1.0, 1.0
    # Convex objective; derivative sign at an active line locates the minimizer.
    for _ in range(70):
        d = (lo + hi) / 2
        line = max(lines, key=lambda row: abs(row[2] + d * row[3]))
        signed_slope = math.copysign(1, line[2] + d * line[3]) * line[3]
        if signed_slope > 0:
            hi = d
        else:
            lo = d
    d = (lo + hi) / 2
    positive, negative = [], []
    for name, t, b, a in lines:
        sign = 1 if b + d * a >= 0 else -1
        item = (sign * (b + d * a), name, t, sign * b, sign * a)
        (positive if sign * a > 0 else negative).append(item)
    left, right = max(negative), max(positive)
    exact_d = (left[3] - right[3]) / (right[4] - left[4])
    value = objective(exact_d, lines)
    dual_weight = right[4] / (right[4] - left[4])
    lower = dual_weight * left[3] + (1 - dual_weight) * right[3]
    assert 0 <= dual_weight <= 1
    assert abs(lower - value) < 2e-12
    assert abs(dual_weight * left[4] + (1 - dual_weight) * right[4]) < 1e-12
    return {
        "d_sigma_c": exact_d,
        "c_seconds": exact_d / SIGMA,
        "peak_m": value,
        "active_lines": [left, right],
        "convex_dual_weight": dual_weight,
        "sampled_minimax_lower_bound_m": lower,
        "sampled_dual_gap_m": value - lower,
    }


def run(step):
    traces = {name: trace(name, step) for name in TRAIN + TEST}
    lines = [(name, t, b, a) for name in TRAIN for t, b, a in traces[name]]
    optimum = solve(lines)
    coefficients = {"zero": 0.0, "nominal": 0.1, "cube": 5 / 48, "tuned": optimum["d_sigma_c"]}
    scores = {
        method: {name: max(abs(b + d * a) for _, b, a in rows) for name, rows in traces.items()}
        for method, d in coefficients.items()
    }
    return {
        "step": step,
        "optimum": optimum,
        "scores_m": scores,
        "train_max_m": {m: max(s[n] for n in TRAIN) for m, s in scores.items()},
        "holdout_max_m": {m: max(s[n] for n in TEST) for m, s in scores.items()},
        "samples_per_scenario": len(traces[TRAIN[0]]),
    }


coarse = run(0.001)
fine = run(0.0005)
result = {
    "parameters": {
        "J": J,
        "h": H,
        "sigma": SIGMA,
        "W": W,
        "horizon": 4 * H + 4,
        "initial_errors": [0, 0, 0],
    },
    "training_rates": TRAIN,
    "heldout_rates": TEST,
    "coarse": coarse,
    "fine": fine,
    "coefficient_refinement_difference": abs(
        coarse["optimum"]["c_seconds"] - fine["optimum"]["c_seconds"]
    ),
    "scope": "Numerical finite scenario/time-grid minimax only. Same original reference, controller, disturbance and initial conditions. No interval enclosure, all-rate guarantee, or physical validation. d=sigma*c.",
}
(HERE / "inventor_minimax.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            "fine": fine,
            "coefficient_refinement_difference": result["coefficient_refinement_difference"],
        },
        indent=2,
    )
)
