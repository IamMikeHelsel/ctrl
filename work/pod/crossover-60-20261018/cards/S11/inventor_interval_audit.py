"""Independent direct-cell interval replay and model-binding mutations."""

import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
S = 10**65


def enclosure(a, b=None):
    b = a if b is None else b
    return a.numerator * S // a.denominator, -((-b.numerator * S) // b.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def times(a, b):
    products = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(products) // S, -((-max(products)) // S)


def rat(a, q):
    return times(a, enclosure(F(q)))


def sub(a, b):
    return add(a, (-b[1], -b[0]))


# Bound exp(+x) by a positive series and geometric tail, then invert.
# This is independent of PM's alternating exp(-x) partial sums.
x = F(1, 250)
term = total = F(1)
for k in range(1, 41):
    term *= x / k
    total += term
tail = (term * x / 41) / (1 - x / 42)
decay = enclosure(1 / (total + tail), 1 / total)
one = enclosure(F(1))
h = F(1, 2000)
iv = rat(sub(one, decay), F(1, 8))
ix = sub(enclosure(h / 8), rat(iv, F(1, 8)))
center = F(2525673, 100000000)
sigma = F(79, 250)


def brake(t):
    return [
        F(1, 1000) + F(39, 100) * t - F(3, 5) * t * t - center,
        F(39, 100) - F(6, 5) * t,
        -F(6, 5),
    ]


def run(mutation=None):
    previous = [enclosure(q) for q in brake(sigma)]
    state = [enclosure(q) for q in brake(sigma + h)]
    if mutation == "clear_acceleration":
        state[2] = (0, 0)
    prefix_binds = state == [enclosure(q) for q in brake(sigma + h)]
    first_command = None
    max_command = 0
    for n in range(21000):
        reading = state if mutation == "use_current_sample" else previous
        command = (0, 0)
        for q, gain in zip(reading, [-8, -6, -F(1, 2)], strict=True):
            command = add(command, rat(q, gain))
        if first_command is None:
            first_command = command
        assert command[0] > -2 * S and command[1] < 2 * S
        max_command = max(max_command, abs(command[0]), abs(command[1]))
        target = add(command, enclosure(F(1 if (n // 2000) % 2 == 0 else -1, 100)))
        # Analytic held-target cell, with the physical current acceleration.
        new_x = add(
            add(state[0], rat(state[1], h)),
            add(times(ix, state[2]), times(sub(enclosure(h * h / 2), ix), target)),
        )
        new_v = add(state[1], add(times(iv, state[2]), times(sub(enclosure(h), iv), target)))
        new_a = add(times(decay, state[2]), times(sub(one, decay), target))
        previous, state = state, [new_x, new_v, new_a]
    return {
        "initial_state_binds": prefix_binds,
        "first_command": [str(F(z, S)) for z in first_command],
        "velocity": [str(F(z, S)) for z in state[1]],
        "velocity_approx": [float(F(z, S)) for z in state[1]],
        "max_command": str(F(max_command, S)),
    }


spec = importlib.util.spec_from_file_location("pm_interval_hold", HERE / "pm_interval_hold.py")
pm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pm)
original = pm.certificate()
result = {
    "pm_independent_execution": original,
    "independent_positive_series_and_direct_cell": run(),
    "wrong_current_sample": run("use_current_sample"),
    "wrong_clear_acceleration": run("clear_acceleration"),
}
baseline = result["independent_positive_series_and_direct_cell"]
assert F(baseline["velocity"][0]) > F(1, 1000)
pm_lo, pm_hi = map(F, original["velocity"])
ind_lo, ind_hi = map(F, baseline["velocity"])
assert max(pm_lo, ind_lo) <= min(pm_hi, ind_hi)
assert result["wrong_current_sample"]["first_command"] != baseline["first_command"]
assert not result["wrong_clear_acceleration"]["initial_state_binds"]
for key in ["wrong_current_sample", "wrong_clear_acceleration"]:
    lo, hi = map(F, result[key]["velocity"])
    assert hi < ind_lo or lo > ind_hi
# PM's optional arbitrary rational duration truncates to complete cells but labels
# the unrounded duration. Its default duration is exactly on-grid and unaffected.
assert int(F(105001, 10000) / h) == 21000
result["duration_interface_boundary"] = (
    "Default21/2 exact; other durations need seconds/h integral guard"
)
(HERE / "inventor_interval_audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(
    json.dumps(
        {
            key: value.get("velocity_approx")
            for key, value in result.items()
            if isinstance(value, dict)
        },
        indent=2,
    )
)
