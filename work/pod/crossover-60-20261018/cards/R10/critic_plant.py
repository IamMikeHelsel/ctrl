"""Independent numerical physical replay in error coordinates, DOP853 not expm."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

HERE = Path(__file__).resolve().parent
cases = json.loads((HERE / "inventor_width.json").read_text())["cases"]
rows = []
for case in cases:
    if "widen" not in case["name"]:
        continue
    deadline = float(F(case["deadline"]))
    goal = float(F(case["deadline_reference_state_q_v_a_j"][0]))
    for rate in [80, 100, 120]:
        for disturbance in [0.0, 0.01]:
            error = np.zeros(3)
            states = []
            for piece in case["piece_certificates"]:
                left, right = map(lambda z: float(F(z)), [piece["start"], piece["end"]])
                ds = np.array([float(F(z)) for z in piece["derivatives"]])

                def rhs(t, e, ds=ds, left=left, rate=rate, disturbance=disturbance):
                    jerk = ds[3] + ds[4] * (t - left)
                    return [
                        e[1],
                        e[2],
                        -rate * (800 * e[0] + 60 * e[1] + 1.5 * e[2])
                        + (rate / 96 - 1) * jerk
                        + rate * disturbance,
                    ]

                sol = solve_ivp(
                    rhs,
                    [left, right],
                    error,
                    method="DOP853",
                    rtol=2e-12,
                    atol=2e-14,
                    dense_output=True,
                )
                assert sol.success
                ts = np.unique(
                    np.r_[
                        np.linspace(left, right, max(2, int(np.ceil((right - left) / 0.0005)) + 1)),
                        [t for t in [0.5, deadline] if left <= t <= right],
                    ]
                )
                errs = sol.sol(ts)
                for i, t in enumerate(ts):
                    z = t - left
                    ref = np.array(
                        [
                            sum(ds[k + n] * z**n / factorial(n) for n in range(5 - k))
                            for k in range(3)
                        ]
                    )
                    states.append((t, *(errs[:, i] + ref)))
                error = sol.y[:, -1]
            post = np.array([s[1:] for s in states if s[0] >= deadline - 1e-14])
            peaks = np.max(np.abs(post - np.array([goal, 0, 0])), axis=0)
            progress = next(s[1] for s in states if abs(s[0] - 0.5) < 1e-14)
            rows.append(
                {
                    "case": case["name"],
                    "rate": rate,
                    "disturbance": disturbance,
                    "progress_m": progress,
                    "endpoint": list(next(s[1:] for s in states if abs(s[0] - deadline) < 1e-14)),
                    "deadline_and_remain_sample_max": peaks.tolist(),
                    "pass": bool(
                        progress >= 0.001 and all(peaks <= np.array([0.0002, 0.001, 0.02]))
                    ),
                }
            )
assert all(r["pass"] for r in rows)
(HERE / "critic_plant.json").write_text(
    json.dumps(
        {
            "rows": rows,
            "scope": "Independent numerical DOP853 error-coordinate integration, no state reset; dense sampled remain, not all-time proof.",
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(rows, indent=2))
