"""Supplemental numerical hold probe; NOT an enclosure or original-reference result."""

import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

rows = []
for T in [0.08, 0.25]:
    for r in [8, 12]:

        def move(t, z, T=T, r=r):
            s = t / T
            j = (60 - 360 * s + 360 * s * s) / T**3
            return [z[1], z[2], -8 * r * z[0] - 6 * r * z[1] - 1.5 * r * z[2] + j]

        sol = solve_ivp(move, [0, T], [0, 0, 0], rtol=1e-11, atol=1e-13, dense_output=True)
        hold = solve_ivp(
            lambda t, z, r=r: [z[1], z[2], -8 * r * z[0] - 6 * r * z[1] - 1.5 * r * z[2]],
            [T, T + 4],
            sol.y[:, -1],
            rtol=1e-11,
            atol=1e-13,
            dense_output=True,
        )
        assert sol.success and hold.success
        ts = np.linspace(T, T + 4, 20001)
        values = hold.sol(ts)[0]
        i = np.argmax(abs(values))
        z = sol.y[:, -1]
        cube = max(abs(z[0]), abs(z[0] + z[1] / 4), abs(z[0] + z[1] / 2 + z[2] / 16))
        rows.append(
            {
                "T": T,
                "r": r,
                "sampled_hold_peak": float(abs(values[i])),
                "peak_time": float(ts[i]),
                "initial_cube_radius": float(cube),
            }
        )
Path(__file__).with_name("domain_hold_probe_results.json").write_text(
    json.dumps(rows, indent=2) + "\n"
)
print(json.dumps(rows, indent=2))
