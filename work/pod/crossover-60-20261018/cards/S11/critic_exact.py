"""Exact source-bound negative controls; no producer implementation imported."""

import json
import math
from fractions import Fraction as F
from pathlib import Path


def exp_negative(t, n=80):
    assert 0 <= t <= 8
    # Positive exponential series plus geometric tail, invert to bound exp(-t).
    s = sum(t**k / math.factorial(k) for k in range(n + 1))
    tail = t ** (n + 1) / math.factorial(n + 1) / (1 - t / (n + 2))
    return 1 / (s + tail), 1 / s


def policy(m):
    w = (F(51, 50), F(101, 100), F(1))
    e = tuple(F(n, 100000000) for n in (101533, 368033, 1042283))
    o = (m[0], m[0] + m[1] / 4, m[0] + m[1] / 2 + m[2] / 16)
    k = max(
        F(9, 200),
        *((o[i] - o[j] + e[i] + e[j]) / (w[i] + w[j]) for i in range(3) for j in range(3)),
    )
    c = max(o[i] + e[i] - w[i] * k for i in range(3))
    return k, c


def guard(m):
    return m[0] <= F(143, 1000) and abs(m[1]) <= F(561, 50000) and F(-127, 100) <= m[2] <= F(-1, 5)


def main():
    tau = F(13, 40)

    def x(t):
        return F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t

    def v(t):
        return F(39, 100) - F(6, 5) * t

    assert v(tau) == 0 and x(tau) == F(103, 1600)
    latency = F(1, 2000)
    assert x(tau + latency) - x(tau) == -F(3, 20000000)
    assert v(tau + latency) == -F(3, 5000)
    sample = F(79, 250)
    m = (x(sample), v(sample), F(-6, 5))
    assert guard(m)
    k, c = policy(m)
    for shift in (F(-1), F(-100), F(-10000)):
        translated = (m[0] + shift, m[1], m[2])
        assert guard(translated) and policy(translated) == (k, c + shift)
        assert F(1, 1000) + shift <= F(1, 1000)
    # Release target to zero at true v=0, a=-1.2: no state reset.
    elo, ehi = exp_negative(F(8))
    velocity = (-F(3, 20) * (1 - elo), -F(3, 20) * (1 - ehi))
    travel = (-F(3, 20) * (1 - (1 - ehi) / 8), -F(3, 20) * (1 - (1 - elo) / 8))
    assert velocity[1] < -F(149, 1000) and travel[1] < -F(13, 100)
    # Start true rest with exact read and u=0, allowed new d=.01 and r8.
    t = F(1, 2000)
    elo, ehi = exp_negative(8 * t)
    acceleration = (F(1, 100) * (1 - ehi), F(1, 100) * (1 - elo))
    speed = (F(1, 100) * (t - (1 - elo) / 8), F(1, 100) * (t - (1 - ehi) / 8))
    displacement = (
        F(1, 100) * (t * t / 2 - t / 8 + (1 - ehi) / 64),
        F(1, 100) * (t * t / 2 - t / 8 + (1 - elo) / 64),
    )
    assert all(b[0] > 0 for b in (acceleration, speed, displacement))
    # Allowed constant sensor and target errors support a nonzero position offset.
    noise = (F(1, 1000), F(1, 100), F(1, 20))
    d = F(1, 100)
    offset = (d - 8 * noise[0] - 6 * noise[1] - noise[2] / 2) / 8
    command = -8 * (offset + noise[0]) - 6 * noise[1] - noise[2] / 2
    assert command + d == 0 and abs(command) <= 2 and offset == -F(83, 8000)
    # Weighted plateau gives bounded motion, not precision rest.
    K = F(9, 200)
    vcap = 4 * (F(51, 50) + F(101, 100)) * K
    acap = 16 * (F(1) + 2 * F(101, 100) + F(51, 50)) * K
    result = {
        "first_zero": str(tau),
        "first_zero_position": str(x(tau)),
        "continued_braking_half_ms_backward_travel": "-3/20000000",
        "release_to_zero_1s": {
            "velocity": list(map(str, velocity)),
            "relative_position": list(map(str, travel)),
        },
        "true_rest_disturbance_half_ms": {
            "a": list(map(str, acceleration)),
            "v": list(map(str, speed)),
            "dx": list(map(str, displacement)),
        },
        "translated_guard_and_center": True,
        "absolute_lower_initial_bound_missing": True,
        "allowed_biased_stationary_offset": str(offset),
        "weighted_plateau_velocity_bound": str(vcap),
        "weighted_plateau_acceleration_bound": str(acap),
        "scope": "First-zero continuation/release and true-rest disturbance are declared controller-mode diagnostics, not claims that actual C8 fails its proved ceiling. Static biased equilibrium satisfies the digital holding law with errors, not necessarily its guard entry.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        "v plateau",
        float(vcap),
        "a plateau",
        float(acap),
        "offset",
        float(offset),
        "rest-cell v",
        float(speed[0]),
    )


if __name__ == "__main__":
    main()
