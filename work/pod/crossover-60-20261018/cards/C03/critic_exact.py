"""Independent exact source-state replay and joint moment-gate counterexample."""

import json
from fractions import Fraction as F
from pathlib import Path


def advance(state, h, snap):
    q, v, a, j = state
    return (
        q + v * h + a * h * h / 2 + j * h**3 / 6 + snap * h**4 / 24,
        v + a * h + j * h * h / 2 + snap * h**3 / 6,
        a + j * h + snap * h * h / 2,
        j + snap * h,
    )


def integrate(coeff, low, high):
    return sum(
        (c * (high ** (i + 1) - low ** (i + 1)) / (i + 1) for i, c in enumerate(coeff)), F(0)
    )


def multiply(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def moment(pieces, kernel):
    return sum((integrate(multiply(poly, kernel), a, b) for a, b, poly in pieces), F(0))


def main():
    initial = (F(5, 192), F(5, 16), F(5, 2), F(10))
    ell = F(1, 200)
    executed = advance(initial, ell, F(0))
    assert executed == (F(44217, 1600000), F(2601, 8000), F(51, 20), F(10))
    state = executed
    for h, s in [(F(1, 20), F(-400)), (F(97, 400), F(0)), (F(1, 40), F(400))]:
        state = advance(state, h, s)
    assert state == (F(8782613, 38400000), F(75089, 96000), F(0), F(0))
    V = state[1]
    L = F(7, 10)
    cruise = F(3744927, 30035600)
    qbrake = state[0] + V * cruise
    assert qbrake + V * L / 2 == F(3, 5)
    stoptime = F(51, 200) + F(127, 400) + cruise + L
    assert stoptime == F(10491307, 7508900) < F(3, 2)
    limits = {
        "accel": 15 * V / (8 * L),
        "jerk_squared": F(100, 3) * V * V / L**4,
        "snap": 60 * V / L**3,
    }
    assert limits["accel"] < 3 and limits["jerk_squared"] < 100 and limits["snap"] < 400
    # Old first a=0 endpoint lacks terminal j constraint; extremal j ends−10.
    low = advance(initial, F(1, 20), F(-400))
    low = advance(low, F(1, 4), F(0))
    assert low == (F(1991, 9600), F(181, 240), F(0), F(-10))
    assert low[0] > F(5, 32) and low[1] > F(5, 8)
    assert F(5, 2) / 10 + 2 * ell + F(20, 400) == F(31, 100)
    assert executed[2] / 10 + F(5 * 10, 2 * 400) == F(127, 400)
    # New diagnostic: all marginal endpoints are individually feasible but not jointly.
    lower = [
        (F(0), F(1, 2), [F(1), F(-4)]),
        (F(1, 2), F(3, 4), [F(-1)]),
        (F(3, 4), F(1), [F(-4), F(4)]),
    ]
    upper = [(F(0), F(3, 4), [F(1)]), (F(3, 4), F(1), [F(4), F(-4)])]
    kernels = [[F(1)], [F(1), F(-1)], [F(1, 2), F(-1), F(1, 2)]]
    bounds = [(moment(lower, k), moment(upper, k)) for k in kernels]
    assert bounds[:2] == [(F(-3, 8), F(7, 8)), (F(-7, 96), F(47, 96))]
    desired = [F(1, 2), F(0), sum(bounds[2]) / 2]
    weights = [(d - lo) / (hi - lo) for d, (lo, hi) in zip(desired, bounds, strict=True)]
    assert all(0 < w < 1 for w in weights)
    # Every marginal witness (1−weight)L+weight U has the same j0=1,jT=0,J1,S4.
    support = integrate(multiply([F(-1), F(2)], [F(1), F(-4)]), F(0), F(1, 2))
    support += integrate([F(-1), F(2)], F(1, 2), F(3, 4))
    support += integrate(multiply([F(-1), F(2)], [F(4), F(-4)]), F(3, 4), F(1))
    assert support == F(1, 16) < desired[0] - 2 * desired[1]
    result = {
        "source_execution_state": list(map(str, executed)),
        "source_blend_state": list(map(str, state)),
        "source_stop_time": str(stoptime),
        "source_brake_bounds": {k: str(v) for k, v in limits.items()},
        "old_zero_accel_endpoint": list(map(str, low)),
        "latency_zero_accel_arrival_duration": "31/100",
        "terminal_zero_jerk_execution_duration": "127/400",
        "joint_diagnostic": {
            "T": "1",
            "J": "1",
            "S": "4",
            "initial_jerk": "1",
            "terminal_jerk": "0",
            "initial_qva": ["0", "0", "0"],
            "marginal_ranges_a_v_q": [[str(x) for x in z] for z in bounds],
            "desired_a_v_q": list(map(str, desired)),
            "individual_feasible_convex_weights": list(map(str, weights)),
            "support_normal_a_v_q": ["1", "-2", "0"],
            "support_upper": "1/16",
            "desired_support": "1/2",
            "scope": "Necessary outer support bound; envelope maximizer need not itself obey snap. Every marginal witness obeys jerk, snap and endpoint jerk.",
        },
        "scope": "Exact reference arithmetic and hand integration/interval bounds, no plant or general trajectory-existence proof.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
