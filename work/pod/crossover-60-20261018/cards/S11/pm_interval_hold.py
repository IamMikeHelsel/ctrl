"""Exact outward fixed-point recurrence; Python certificate, not Lean proof.

Taylor's alternating-series enclosure bounds exp(-1/250). All subsequent
operations use integer intervals with outward rounding. The retained six
coordinates bind current and one-sample-old physical states.
"""

import json
from fractions import Fraction as Q
from pathlib import Path

S = 10**60
HERE = Path(__file__).resolve().parent


def enc(q):
    return (q.numerator * S // q.denominator, -((-q.numerator * S) // q.denominator))


def plus(*xs):
    return sum(x[0] for x in xs), sum(x[1] for x in xs)


def mul(a, b):
    p = [x * y for x in a for y in b]
    return min(p) // S, -((-max(p)) // S)


def scale(a, q):
    return mul(a, enc(q))


def bounds(a):
    return [str(Q(x, S)) for x in a]


def certificate(seconds=Q(21, 2)):
    h, r = Q(1, 2000), Q(8)
    cells = Q(seconds) / h
    if cells.denominator != 1 or cells < 0:
        raise ValueError("Certificate time must be a nonnegative integer number of cells")
    term, partial = Q(1), Q(1)
    for k in range(1, 61):
        term *= -r * h / k
        partial += term
    # Even partial sum above exp; next odd partial below. Terms decrease.
    lo, hi = partial + term * (-r * h) / 61, partial
    e = (enc(lo)[0], enc(hi)[1])
    one, zero = enc(Q(1)), (0, 0)
    f12 = scale(plus(one, scale(e, -1)), 1 / r)
    f02 = plus(enc(h / r), scale(f12, -1 / r))
    f = [[one, enc(h), f02], [zero, one, f12], [zero, zero, e]]
    b = [
        plus(enc(h * h / 2), scale(f02, -1)),
        plus(enc(h), scale(f12, -1)),
        plus(one, scale(e, -1)),
    ]
    gain = [Q(8), Q(6), Q(1, 2)]
    t = [f[i] + [scale(b[i], -g) for g in gain] for i in range(3)]
    t += [[one if i == j else zero for j in range(6)] for i in range(3)]
    center, sigma = Q(2525673, 10**8), Q(79, 250)

    def brake(tm):
        return [
            Q(1, 1000) + Q(39, 100) * tm - Q(3, 5) * tm**2 - center,
            Q(39, 100) - Q(6, 5) * tm,
            -Q(6, 5),
        ]

    state = [enc(q) for q in brake(sigma + h) + brake(sigma)]
    max_command = Q(0)
    for n in range(int(cells)):
        command = plus(*(scale(state[3 + i], -gain[i]) for i in range(3)))
        assert command[0] > -2 * S and command[1] < 2 * S, (
            "linear recurrence invalid if clip active"
        )
        max_command = max(max_command, Q(max(abs(command[0]), abs(command[1])), S))
        d = Q(1 if (n // 2000) % 2 == 0 else -1, 100)
        state = [
            plus(*(mul(t[i][j], state[j]) for j in range(6)), scale(b[i], d) if i < 3 else zero)
            for i in range(6)
        ]
    assert state[1][0] > S // 1000
    return {
        "elapsed_after_arrival": str(seconds),
        "global_time": str(sigma + h + seconds),
        "position_minus_center": bounds(state[0]),
        "velocity": bounds(state[1]),
        "acceleration": bounds(state[2]),
        "velocity_approx": [float(Q(x, S)) for x in state[1]],
        "max_command_bound": str(max_command),
        "exp_enclosure": [str(lo), str(hi)],
        "steps": int(cells),
        "claim": "Exact Python outward interval proves sampled velocity > .001 m/s at this time for the stated linear delayed recurrence, with clipping inactive at every cell. Source/model binding reviewed separately; no periodic-limit or Lean claim.",
    }


if __name__ == "__main__":
    result = certificate()
    (HERE / "pm_interval_hold.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
