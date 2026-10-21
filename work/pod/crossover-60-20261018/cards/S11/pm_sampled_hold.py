"""Numerical actual-C8-prefix continuation; not an interval or kernel certificate."""

import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm

HERE = Path(__file__).resolve().parent
H = 0.0005
C = 2525673 / 100000000
SIGMA = 0.316
GAIN = np.array([8.0, 6.0, 0.5])


def brake(t):
    return np.array([0.001 + 0.39 * t - 0.6 * t * t, 0.39 - 1.2 * t, -1.2])


def run(disturbance, rate=8.0, seconds=80):
    # Held input matrix; target=clipped command + independent target error.
    a = np.zeros((4, 4))
    a[0, 1], a[1, 2], a[2, 2], a[2, 3] = 1, 1, -rate, rate
    flow = expm(H * a)
    previous, state = brake(SIGMA), brake(SIGMA + H)
    samples, commands = [state.copy()], []
    for n in range(int(seconds / H)):
        command = np.clip(-GAIN @ (previous - np.array([C, 0, 0])), -2, 2)
        # Sample at sigma+n*h controls cell starting sigma+(n+1)*h.
        target = command + disturbance(n)
        following = (flow @ np.append(state, target))[:3]
        previous, state = state, following
        samples.append(state.copy())
        commands.append(float(command))
    rows = np.array(samples)
    tail = rows[-int(10 / H) :]
    return {
        "rate": rate,
        "horizon_after_arrival_seconds": seconds,
        "sampled_position_min_max": [float(rows[:, 0].min()), float(rows[:, 0].max())],
        "tail_position_min_max": [float(tail[:, 0].min()), float(tail[:, 0].max())],
        "tail_velocity_min_max": [float(tail[:, 1].min()), float(tail[:, 1].max())],
        "tail_acceleration_min_max": [float(tail[:, 2].min()), float(tail[:, 2].max())],
        "max_abs_command": float(np.max(np.abs(commands))),
        "final_state": rows[-1].tolist(),
        "first_command": commands[0],
    }


if __name__ == "__main__":
    results = {
        "scope": "Numerical grid observations; same C8 braking prefix and first reading, zero future sensor errors; permitted constant cell rates/target errors. Not continuous enclosure, periodic-limit proof or hardware validation.",
        "center": C,
        "square_wave": "target error +.01 for 1s, -.01 for 1s, repeating from first hold cell",
        "cases": {
            "zero": run(lambda n: 0),
            "constant_positive": run(lambda n: 0.01),
            "square_r8": run(lambda n: 0.01 if (n // 2000) % 2 == 0 else -0.01),
            "square_r12": run(lambda n: 0.01 if (n // 2000) % 2 == 0 else -0.01, 12),
        },
    }
    (HERE / "pm_sampled_hold.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
