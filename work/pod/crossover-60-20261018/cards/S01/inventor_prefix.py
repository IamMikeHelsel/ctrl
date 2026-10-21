"""Exact source-shaped prefix/clock term checks, not an ODE existence proof."""

import json
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).parent
h = F(1, 2000)


def grid(n):
    return n * h


def index(right, t):
    u = (t - h) / h
    return (
        max(0, u.numerator // u.denominator)
        if right
        else max(0, -((-u.numerator) // u.denominator) - 1)
    )


@lru_cache(None)
def state(n, t):
    if n == 0:
        return ("pending_full_state", str(t))
    if t <= grid(n):
        return state(n - 1, t)
    reading = measure(n - 1, n - 1)
    return (
        "exact_held_flow",
        ("rate", n),
        str(t - grid(n)),
        ("clipped_command_plus_delta", reading, n),
        state(n - 1, grid(n)),
    )


def measure(n, j):
    return (
        ("authoritative_m",)
        if j == 0
        else ("state_plus_sensor_error", state(n, grid(j)), ("epsilon", j))
    )


def reading(n, right, t):
    return measure(n, index(right, t))


checks = 0
selector_checks = 0
for M in range(1, 15):
    for k in range(4 * M + 1):
        t = F(k, 4) * h
        scaled = t / h
        selected = -((-scaled.numerator) // scaled.denominator)
        assert selected <= M
        assert grid(selected + 1) - t >= h
        assert state(selected, t) == state(M, t)
        selector_checks += 1
for N in range(2, 12):
    for M in range(N, 15):
        times = {F(k, 4) * h for k in range(4 * N + 1)}
        for t in times:
            assert state(N - 1, t) == state(M - 1, t)
            for side in [False, True]:
                assert reading(N - 1, side, t) == reading(M - 1, side, t)
                j = index(side, t)
                assert 0 <= grid(j) <= t and t - grid(j) <= 2 * h
                assert j <= N - 1
                checks += 1
for n in range(1, 30):
    t = grid(n + 1)
    assert index(False, t) == n - 1 and index(True, t) == n
    assert t - grid(index(False, t)) == 2 * h
    assert t - grid(index(True, t)) == h
# The new Nth cell cannot supply the outgoing ODE from the old finite horizon.
N = 4
assert state(N - 1, grid(N)) == state(N, grid(N))
assert state(N - 1, grid(N) + h / 10) != state(N, grid(N) + h / 10)
# The previous comparison outside [0,N*h] is only a negative control on
# finite formula extrapolation, not a statement that the old formula is valid there.
for k in [0, 632, 1058]:
    for j in range(15):
        assert grid(k) + grid(j) == grid(k + j)
        assert grid(k) + h + grid(j) == grid(k + j + 1)
for T in [F(0), h / 2, h, 2 * h, F(1), F(17, 1000)]:
    count = T // h
    assert grid(count) <= T < grid(count + 1)
result = {
    "state_reading_side_checks": checks,
    "diagonal_selector_checks": selector_checks,
    "selector_finite_horizon_buffer_at_least": str(h),
    "fixed_stream_prefix_compatible": True,
    "clock_h": str(h),
    "dispatch_spacing": str(h),
    "dispatch_boundary_ages": {"incoming": str(2 * h), "outgoing": str(h)},
    "same_final_state_but_distinct_extrapolation_terms": True,
    "translated_clock_examples": [0, 632, 1058],
    "scope": "Exact rational indexing and structural equality of full-state/reading recurrence terms mirroring source definitions. heldSolution remains an uninterpreted exact-flow term; this tests dependency/prefix structure, not differential equations, safety, or global existence.",
}
(HERE / "inventor_prefix.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
