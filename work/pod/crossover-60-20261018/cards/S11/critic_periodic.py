"""Exact rational parameter enclosure for a hand-derived periodic hold countermodel."""

import json
from fractions import Fraction as F
from pathlib import Path

from critic_exact import exp_negative

h = F(1, 2000)
r = F(8)
A = F(1, 100000)
E = exp_negative(r * h)
C = tuple((1 + e) / (1 - e) for e in E)
D = (2 / r - C[1] * h, 2 / r - C[0] * h)
assert D[1] < 0
# delta amplitude = A*(C+.5+D*(4/r-3)) = A*((801/800)*C-1/8).
delta = tuple(A * (F(801, 800) * c - F(1, 8)) for c in C)
assert 0 < delta[0] <= delta[1] < F(1, 100)
velocity = (-D[1] * A / 2, -D[0] * A / 2)
position = (D[0] * A / (2 * r), D[1] * A / (2 * r))
command = (A * (F(1, 2) - F(5, 2) * D[1]), A * (F(1, 2) - F(5, 2) * D[0]))
assert max(map(abs, command)) < 2 and velocity[0] > 0
out = {
    "h": str(h),
    "r": str(r),
    "A": str(A),
    "E_interval": list(map(str, E)),
    "C_interval": list(map(str, C)),
    "D_interval": list(map(str, D)),
    "disturbance_amplitude_interval": list(map(str, delta)),
    "positive_boundary_velocity_interval": list(map(str, velocity)),
    "positive_a_boundary_position_offset_interval": list(map(str, position)),
    "command_interval": list(map(str, command)),
    "float_summary": {
        "delta": float(delta[0]),
        "speed": float(velocity[0]),
        "position": float(position[0]),
    },
    "evidence": "Exact rational bounds on exp(-rh) and explicit hand-derived held-flow algebra, not a Lean periodic-execution theorem.",
    "scope": "Period-two terminal-state/history countermodel with one-cell delayed exact readings. No claim of reachability from actual C8 guard/pending prefix; initialization must include matching delayed controller history.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(out["float_summary"])
