"""Exact structural negative controls; these are not C8 physical counterexamples."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).parent
h = F(1, 2000)
# An infinitely branching tree has arbitrarily long finite paths but no infinite path:
# root chooses a natural n, then strictly counts down to zero, where it terminates.
paths = [["root"] + list(range(n, -1, -1)) for n in range(1, 51)]
assert all(all(a == b + 1 for a, b in zip(p[1:-1], p[2:], strict=True)) for p in paths)
assert all(p[0] == "root" for p in paths)
assert all(a[1] != b[1] for a, b in zip(paths[:-1], paths[1:], strict=True))
# Every positive step alone does not imply non-Zeno.
zeno = []
s = F(0)
for n in range(1, 101):
    step = h / 2**n
    s += step
    assert step > 0 and s == h * (1 - F(1, 2**n)) and s < h
    zeno.append(str(s))


# Original grid floor/right and ceil-minus-one/left; terminal derivatives use different cells.
def index(right, t):
    x = 2000 * (t - h)
    return (
        max(0, x.numerator // x.denominator)
        if right
        else max(0, -((-x.numerator) // x.denominator) - 1)
    )


index_rows = []
for N in range(2, 51):
    t = N * h
    assert index(True, t) == N - 1 and index(False, t) == N - 2
    assert index(True, t + h / 3) == N - 1
    index_rows.append({"N": N, "right": index(True, t), "left": index(False, t)})


# Local source command equation: same physical state, differing permitted acceleration reading.
def command(c, s):
    return max(F(-2), min(F(2), -8 * (s[0] - c) - 6 * s[1] - s[2] / 2))


reading_a = (F(0), F(0), F(1, 20))
reading_b = (F(0), F(0), -F(1, 20))
u_a, u_b = command(F(0), reading_a), command(F(0), reading_b)
assert u_a == -F(1, 40) and u_b == F(1, 40)
assert 8 * u_a == -F(1, 5) and 8 * u_b == F(1, 5)
# Equal physical seam state does not identify reading/error streams or outgoing derivatives.
# Common half-ms latency preserves strict sample order; independently varying [0,h] can tie.
assert 0 + h < h + h
assert 0 + h == h + 0
# Preserving readings strictly before k, but not the guard sample k, is insufficient.
old = [False] * 632 + [True] + [False] * 3
changed = old.copy()
changed[632] = False
changed[633] = True
assert old[:632] == changed[:632]
assert old.index(True) == 632 and changed.index(True) == 633
out = {
    "scope": "Exact synthetic countermodels to weakened premises; no refutation of original finite C7/C8 theorem.",
    "incompatible_prefix_lengths": [len(p) for p in paths],
    "positive_zeno_steps": 100,
    "zeno_horizon_upper_s": str(h),
    "terminal_indices": index_rows,
    "same_state_distinct_reading_commands": [str(u_a), str(u_b)],
    "outgoing_jerks": [str(8 * u_a), str(8 * u_b)],
    "variable_latency_tie_s": str(h),
    "guard_first_old": 632,
    "guard_first_changed": 633,
}
(HERE / "critic_negative.json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            k: v
            for k, v in out.items()
            if k not in ["terminal_indices", "incompatible_prefix_lengths"]
        },
        indent=2,
    )
)
