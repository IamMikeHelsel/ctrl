"""Exact kinematic ZOH allocation; no dynamic torque or hardware assertion."""

import json
from fractions import Fraction as F
from pathlib import Path


def interval(q, task_rate, horizon, input_limit, halfspaces):
    assert horizon > 0 and input_limit >= 0
    v, T, U = task_rate, horizon, input_limit
    constraints = [
        (F(1), U - v / 2, "u1 upper"),
        (-F(1), U + v / 2, "u1 lower"),
        (-F(1), U - v / 2, "u2 upper"),
        (F(1), U + v / 2, "u2 lower"),
    ]
    initial_safe = all(a * q[0] + b * q[1] <= c for a, b, c in halfspaces)
    for i, (a, b, c) in enumerate(halfspaces):
        constraints.append(
            (T * (a - b), c - a * q[0] - b * q[1] - T * (a + b) * v / 2, f"endpoint {i}")
        )
    lo = max(beta / alpha for alpha, beta, _ in constraints if alpha < 0)
    hi = min(beta / alpha for alpha, beta, _ in constraints if alpha > 0)
    feasible = (
        initial_safe and lo <= hi and all(beta >= 0 for alpha, beta, _ in constraints if alpha == 0)
    )
    return lo, hi, feasible, constraints


def check(name, q, v, T, U, n0, halfspaces, expected):
    lo, hi, feasible, rows = interval(q, v, T, U, halfspaces)
    assert feasible == expected
    result = {
        "name": name,
        "q": q,
        "task_rate": v,
        "horizon": T,
        "input_limit": U,
        "nominal_null_coordinate": n0,
        "halfspaces": halfspaces,
        "lo": lo,
        "hi": hi,
        "feasible": feasible,
        "scalar_constraints": rows,
    }
    if feasible:
        n = min(hi, max(lo, n0))
        u = (v / 2 + n, v / 2 - n)
        assert u[0] + u[1] == v
        assert all(alpha * n <= beta for alpha, beta, _ in rows)
        assert all(-U <= x <= U for x in u)
        endpoint = tuple(qi + T * ui for qi, ui in zip(q, u, strict=True))
        assert all(
            a * q[0] + b * q[1] <= c and a * endpoint[0] + b * endpoint[1] <= c
            for a, b, c in halfspaces
        )
        # The Lean affine-segment theorem upgrades these endpoints to all times.
        assert (n == n0) == (lo <= n0 <= hi)
        for m in [lo, hi, (lo + hi) / 2]:
            assert 2 * (n - n0) ** 2 <= 2 * (m - n0) ** 2
        result.update(
            selected_null_coordinate=n,
            selected_velocity=u,
            endpoint=endpoint,
            intervention_squared=2 * (n - n0) ** 2,
        )
    return result


def encode(obj):
    if isinstance(obj, F):
        return str(obj)
    if isinstance(obj, tuple):
        return [encode(x) for x in obj]
    if isinstance(obj, list):
        return [encode(x) for x in obj]
    if isinstance(obj, dict):
        return {k: encode(v) for k, v in obj.items()}
    return obj


if __name__ == "__main__":
    box = [(F(1), F(0), F(1)), (-F(1), F(0), F(0)), (F(0), F(1), F(1)), (F(0), -F(1), F(0))]
    safe = box + [(F(1), -F(1), F(0))]
    q = (F(2, 5), F(3, 5))
    cases = [
        check("do not correct joint displacement", q, F(0), F(1), F(1, 4), F(0), safe, True),
        check("retain safe null motion", q, F(0), F(1), F(1, 4), F(1, 10), safe, True),
        check(
            "correct obstacle-threatening null motion", q, F(0), F(1), F(1, 4), F(1, 5), safe, True
        ),
        check("impossible task speed", q, F(3, 10), F(1), F(1, 10), F(0), safe, False),
        check(
            "already unsafe cannot certify prefix",
            (F(3, 5), F(2, 5)),
            F(0),
            F(1),
            F(1, 4),
            F(-1, 5),
            safe,
            False,
        ),
    ]
    fiber = []
    for v in [F(0), F(1, 10)]:
        for q1 in [F(1, 10), F(1, 5), F(2, 5), F(1, 2)]:
            row = check(
                "task-only nominal fiber equivariance",
                (q1, 1 - q1),
                v,
                F(1),
                F(1, 4),
                F(0),
                safe,
                True,
            )
            assert row["selected_velocity"] == (v / 2, v / 2)
            assert row["endpoint"][0] - row["endpoint"][1] == 2 * q1 - 1
            fiber.append(row)
    active = check(
        "fiber symmetry broken only by active joint constraint",
        (F(0), F(1)),
        F(1, 10),
        F(1),
        F(1, 4),
        F(0),
        safe,
        True,
    )
    assert active["selected_velocity"] == (F(1, 10), F(0))
    # Predetermined grid, including empty feasible sets and zero-normal rows.
    count = 0
    for a in range(5):
        for b in range(a, 5):
            for vi in range(-4, 5):
                v = F(vi, 10)
                qg = (F(a, 4), F(b, 4))
                lo, hi, ok, rows = interval(qg, v, F(1, 2), F(1, 4), safe)
                for n in [F(i, 20) for i in range(-10, 11)]:
                    direct = all(alpha * n <= beta for alpha, beta, _ in rows)
                    reduced = ok and lo <= n <= hi
                    assert direct == reduced
                    count += 1
    out = {
        "model": "exact first-order qdot=u, ZOH, fixed one-step horizon",
        "no_dynamic_or_hardware_claim": True,
        "cases": cases,
        "task_only_nominal_fiber_tests": fiber,
        "active_constraint_fiber_exception": active,
        "grid_equivalences": count,
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(encode(out), indent=2) + "\n")
    print(f"{len(cases)} exact fixtures and {count} interval/direct equivalences passed")
