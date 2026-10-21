"""Semantic negative controls for held saturated dynamics; exact exp enclosures."""

import json
from fractions import Fraction as F
from pathlib import Path


def negexp(t):
    # Alternating series at 0<=t<=1: even sum upper, following odd lower.
    assert 0 <= t <= 1
    s = F(1)
    term = F(1)
    for k in range(1, 81):
        term *= -t / k
        s += term
    nxt = term * (-t) / 81
    return s + nxt, s


h = F(1, 5)
elo, ehi = negexp(h)
flo, fhi = negexp(h / 2)
# z=(0,0,1), sampled request=-2, clamp=-1.
# Moving +.01 from after clamp to before clamp erases it.
placement_lo = F(1, 100) * (1 - ehi)
placement_hi = F(1, 100) * (1 - elo)
assert 0 < placement_lo < placement_hi
# w=+.01 first half, -.01 second half has mean0 but final response
# differs from held w0 by -.01*(1-exp(-h/2))^2.
switch_lo = -F(1, 100) * (1 - flo) ** 2
switch_hi = -F(1, 100) * (1 - fhi) ** 2
assert switch_lo < switch_hi < 0
# Merely allowing alpha in[1/4,1] does not give held alpha formula.
# input frozen at-2, alpha1/4 then1: a difference from mean alpha5/8
# is (u2-u1)/2*(1-exp(-h/2))^2 =-.75*(1-e)^2.
gain_lo = -F(3, 4) * (1 - flo) ** 2
gain_hi = -F(3, 4) * (1 - fhi) ** 2
assert gain_lo < gain_hi < 0
P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
z = [F(1, 2)] * 3
full = sum(z[i] * P[i][j] * z[j] for i in range(3) for j in range(3))
diag = sum(z[i] ** 2 * P[i][i] for i in range(3))
assert diag < 12 < full
# Positive but decreasing dwell is not all-time clock coverage.
# h_n=(1/5)*2^(-n-1) all <=.2, totaltime=.2.
assert sum((F(1, 5) * F(1, 2) ** (n + 1) for n in range(30)), F(0)) < F(1, 5)
# Endpoint-only scalar sample safety is logically insufficient: x(t)=3*4t(1-t),
# endpoint0 inside|x|<=2 but interior3; not claimed source plant execution.
assert 3 * 4 * F(1, 2) * (1 - F(1, 2)) == 3
out = {
    "placement_final_acceleration_difference": [str(placement_lo), str(placement_hi)],
    "switch_disturbance_difference": [str(switch_lo), str(switch_hi)],
    "switch_sector_gain_difference": [str(gain_lo), str(gain_hi)],
    "invalid_diagonal_admission": {
        "state": ["1/2"] * 3,
        "diagonal_energy": str(diag),
        "actual_energy": str(full),
    },
    "clock_negative": "h_n=.2*2^(-n-1) has positive every step but finite total. Source uniform positive hmin rules this out.",
    "sampling_negative": "Polynomial endpoint0/interior3 is only a logical negative, not source dynamics. Source already proves all elapsed times.",
    "scope": "Exact difference identities and rational exp brackets; not counterexamples to source theorem. Variable within-cell disturbances/gains need different response proof.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "placement_float": [float(placement_lo), float(placement_hi)],
            "switch_w_float": [float(switch_lo), float(switch_hi)],
            "switch_gain_float": [float(gain_lo), float(gain_hi)],
            "wrong_diagonal": [str(diag), str(full)],
        }
    )
)
