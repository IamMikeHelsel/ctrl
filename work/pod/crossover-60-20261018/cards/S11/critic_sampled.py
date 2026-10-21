"""Independent scalar held-flow replay of the actual C8-prefix numerical probe."""

import json
import math
from pathlib import Path

H = 0.0005
C = 0.02525673


def brake(t):
    return (0.001 + 0.39 * t - 0.6 * t * t, 0.39 - 1.2 * t, -1.2)


def run(rate):
    # Use analytic held-flow scalar integrals, no numpy, expm, or producer imports.
    E = math.exp(-rate * H)
    I = -math.expm1(-rate * H) / rate
    II = (H - I) / rate
    prev = brake(0.316)
    state = brake(0.3165)
    lo = list(state)
    hi = list(state)
    tail_lo = [float("inf")] * 3
    tail_hi = [-float("inf")] * 3
    cmdmax = 0
    for n in range(160000):
        u = max(-2.0, min(2.0, -8 * (prev[0] - C) - 6 * prev[1] - 0.5 * prev[2]))
        if n == 0:
            first = u
        d = 0.01 if (n // 2000) % 2 == 0 else -0.01
        b = u + d
        x, v, a = state
        nxt = (x + v * H + b * H * H / 2 + (a - b) * II, v + b * H + (a - b) * I, b + (a - b) * E)
        prev, state = state, nxt
        for i in range(3):
            lo[i] = min(lo[i], state[i])
            hi[i] = max(hi[i], state[i])
            if n + 1 >= 140001:
                tail_lo[i] = min(tail_lo[i], state[i])
                tail_hi[i] = max(tail_hi[i], state[i])
        cmdmax = max(cmdmax, abs(u))
    assert abs(first - 0.22264264) < 1e-14
    return {
        "rate": rate,
        "first_command": first,
        "final_state": state,
        "sampled_position_min_max": [lo[0], hi[0]],
        "max_abs_command": cmdmax,
        "tail_position_min_max": [tail_lo[0], tail_hi[0]],
        "tail_velocity_min_max": [tail_lo[1], tail_hi[1]],
        "tail_acceleration_min_max": [tail_lo[2], tail_hi[2]],
    }


if __name__ == "__main__":
    p = Path(__file__).resolve().parent
    rows = [run(8), run(12)]
    for row in rows:
        assert max(map(abs, row["tail_velocity_min_max"])) > 0.001
    comparison = {}
    if (p / "pm_sampled_hold.json").exists():
        source = json.loads((p / "pm_sampled_hold.json").read_text())["cases"]
        for row in rows:
            other = source["square_r" + str(row["rate"])]
            differences = {
                k: max(abs(a - b) for a, b in zip(row[k], other[k], strict=True))
                for k in (
                    "final_state",
                    "tail_position_min_max",
                    "tail_velocity_min_max",
                    "tail_acceleration_min_max",
                )
            }
            assert max(differences.values()) < 1e-9
            comparison[str(row["rate"])] = differences
    out = {
        "scope": "Binary64 numerical replay of actual C8 prefix with bounded original sampled-hold rate/disturbance and exact future sensor readings. No continuous certificate or proved periodic limit.",
        "sigma": ".316",
        "arrival": ".3165",
        "h": ".0005",
        "sample_clock": "sigma+n*h",
        "dispatch_clock": "sigma+(n+1)*h",
        "disturbance": "alternating +.01/- .01, 2000 cells each, beginning at first hold cell",
        "rows": rows,
        "producer_comparison": comparison,
    }
    (p / "critic_sampled.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))
