"""Independent half-beat failure and prospective finite correction-ramp audit."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
# Half-beat L=(exp(i*pi)-1)/(i*pi)=2i/pi; w1/2,d1/4.
# z=1/2+i/(2pi), b3/4. Bounds use only3<pi<4.
assert F(1, 16) + F(1, 36) == F(13, 144) < F(31, 100) ** 2
Kupper = F(41, 100)
Bupper = (F(1, 40) + Kupper / 99) / (1 - F(1, 99))
assert Bupper < F(3, 100)
assert Kupper + 2 * Bupper < F(47, 100) < F(3, 4)
# Actual residual1/(2pi)>1/8 becausepi<4; the fictitious leakage bound fails.
assert F(1, 8) > F(1, 99)


def phi(s):
    return 10 * s**3 - 15 * s**4 + 6 * s**5


def deriv(s):
    return 30 * s * s * (1 - s) ** 2


# Complete analytic bound: phi'=30s²(1-s)²>=0; endpoint0,1.
# 4s(1-s)=1-(2s-1)²<=1, so |c'|=15[s(1-s)]²<=15/16.
assert phi(F(0)) == 0 and phi(F(1)) == 1
for s in [F(k, 100) for k in range(101)]:
    assert 4 * s * (1 - s) == 1 - (2 * s - 1) ** 2
    assert 0 <= phi(s) <= 1
    assert deriv(s) / 2 <= F(15, 16) < 1
assert deriv(F(1, 2)) / 2 == F(15, 16)
assert phi(F(2)) == 32  # Extrapolating outside[0,1] violates the proposed amplitude.
assert 2 * F(15, 16) > 1  # A half-second time-compression violates the proposed slew1.
time_upper = 27 + 20 * F(22, 7)
assert time_upper == F(629, 7) < 90
out = {
    "status": "pass",
    "halfbeat_false_wheel_gate_upper": str(Bupper),
    "halfbeat_false_mixed_gate_upper": str(Kupper + 2 * Bupper),
    "halfbeat_actual_failure": "1/(2pi)>1/8; complex analytic measurement exact, window changed",
    "ramp_amplitude": str(F(1, 2)),
    "ramp_slew": str(F(15, 16)),
    "deadline_upper_using_pi22over7": str(time_upper),
    "scope": "One-second force-phasor correction for positive fixturez1/2, with constant tails and ideal authorized actuator. Not a moving-wheel mass attachment, no physical actuator validation or jerk constraint.",
    "negative_controls": [
        "half-beat applied to one-beat certificate",
        "quintic extrapolation afters1",
        "half-second ramp compression",
    ],
}
(P / "critic_final.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
