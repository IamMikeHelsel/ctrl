"""Exact budget arithmetic for root's declared two-axis force-sensor toy interface."""

import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions required")

wheel = F(123, 3920)
nuisance = F(495, 784)
force = wheel + nuisance
assert force == F(1299, 1960) < F(3, 4)
# This sum uses observed centerz=1/2 and correctionc=-1/2.
# Unit phase multipliers preserve the two complex norms.
for gamma in [F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]:
    ramp_bound = (1 - gamma) * 4 + gamma * force
    assert force <= ramp_bound <= 4
# Scalar comparison at a>=1 and retained |x|,|y|<=4:
# X(s)=F+(4-F)*(1+s)*exp(-s), Y(s)=F+(4-F)*exp(-s).
# Y'=-Y+F, X'=-X+Y, and X(0)=Y(0)=4.
# Positive convolution kernels establish the same upper bounds for complex norms.
e6_lower = sum(F(6**k, factorial(k)) for k in range(10))
x6_upper = force + (4 - force) * 7 / e6_lower
y6_upper = force + (4 - force) / e6_lower
assert x6_upper < F(3, 4)
assert force < y6_upper < x6_upper < 4
# Bounds approach nonzero F, not rest. A permissible sustained harmonic force
# at a=1,omega=1 has particular x=F/(1+i)^2*exp(it) with amplitudeF/2.
persistent_amplitude = force / 2
assert persistent_amplitude > 0
out = {
    "status": "pass",
    "sensor": "direct two-axis/vector force, encoded complex",
    "force_post": str(force),
    "ramp_bound": "(1-gamma)*4+gamma*Fpost<=4",
    "post_handoff_position": "Fpost+(4-Fpost)*(1+s)*exp(-s)",
    "post_handoff_y": "Fpost+(4-Fpost)*exp(-s)",
    "x6_rational_upper": str(x6_upper),
    "y6_rational_upper": str(y6_upper),
    "e6_lower": str(e6_lower),
    "persistent_harmonic_position_amplitude": str(persistent_amplitude),
    "scope": "Declared constant-a isotropic complex oscillator; hand variation-of-constants "
    "comparison plus exact arithmetic, no kernel ODE proof. Continuing force is "
    "safe under this envelope but does not imply rest. Physical sensor, phase "
    "actuation, and speed-squared force interface remain unvalidated.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
