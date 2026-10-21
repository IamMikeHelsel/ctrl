"""Declared counterexample to finite jet-query completeness, not a native Ruckig output."""

import json
from fractions import Fraction as F
from pathlib import Path


def advance(state, j, h):
    p, v, a = state
    return [p + v * h + a * h * h / 2 + j * h**3 / 6, v + a * h + j * h * h / 2, a + j * h]


def at(pieces, t):
    for p in pieces:
        if p["lo"] <= t < p["hi"]:
            return advance(p["state"], p["jerk"], t - p["lo"])
    return [F(0)] * 3


start, eps, amplitude = F(3331, 10000), F(1, 10000), F(5, 2)
state = [F(0)] * 3
pieces = []
for k, c in enumerate([1, -3, 3, -1]):
    jerk = amplitude * c
    pieces.append(
        {"lo": start + k * eps, "hi": start + (k + 1) * eps, "state": state, "jerk": jerk}
    )
    state = advance(state, jerk, eps)
assert state == [0, 0, 0]
assert max(abs(p["jerk"]) for p in pieces) == F(15, 2)
queries = [F(k, 1000) for k in range(1001)]
assert all(at(pieces, t) == [0, 0, 0] for t in queries)
assert at(pieces, start + eps)[2] != 0
jerks = [F(0)] + [p["jerk"] for p in pieces] + [F(0)]
jumps = [y - x for x, y in zip(jerks[:-1], jerks[1:], strict=True)]
jerk_tv = sum(abs(x) for x in jumps)
assert jerk_tv == 16 * amplitude == 40
command_jump_tv = jerk_tv / 96
assert command_jump_tv == F(5, 12)
# Exact jerk moment cancellation proves q,v,a reset without inserting state reset.
moments = [
    sum(
        p["jerk"] * ((p["hi"] - start) ** (r + 1) - (p["lo"] - start) ** (r + 1)) / (r + 1)
        for p in pieces
    )
    for r in range(3)
]
assert moments == [0, 0, 0]
output = {
    "scope": "Changed piecewise-cubic diagnostic in source jerk-bound class; not claimed to be a Ruckig-generated trajectory.",
    "pieces": pieces,
    "end_state": state,
    "jerk_moments_0_1_2": moments,
    "sample_count": len(queries),
    "sample_step": F(1, 1000),
    "sampled_qva_difference": 0,
    "jerk_tv": jerk_tv,
    "command_jump_tv": command_jump_tv,
    "continuous_command_TV": "Not computed; nonnegative and separate from jump contribution.",
    "hidden_nonzero_state": at(pieces, start + eps),
    "meaning": "Finite q/v/a samples cannot certify preservation of event support or total variation over this larger trajectory class.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(output, default=str, indent=2) + "\n")
print(
    {
        "query_count": len(queries),
        "zero_query_differences": True,
        "exact_end_state": state,
        "jerk_bound": 7.5,
        "command_jump_TV": str(command_jump_tv),
    }
)
