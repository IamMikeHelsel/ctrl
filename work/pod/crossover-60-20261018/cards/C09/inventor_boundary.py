"""Gaussian-rational checks of the finite-window oscillator boundary correction."""

import json
from fractions import Fraction as F
from pathlib import Path


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def div(z, w):
    n = w[0] ** 2 + w[1] ** 2
    return ((z[0] * w[0] + z[1] * w[1]) / n, (z[1] * w[0] - z[0] * w[1]) / n)


count = 0
for a in [F(1), F(3, 2), F(2)]:
    for omega in [F(0), F(1), F(3)]:
        for endpoint_symbol in [(F(1, 3), F(0)), (F(2, 5), F(1, 7))]:
            for horizon in [F(1), F(7)]:
                # For free decay x=e^-at, z=e^(-(a+iomega)T).
                # Treat z as a formal endpoint value: rational substitutions test
                # the algebra; they are not claimed to be physical exponential values.
                z = endpoint_symbol
                factor = a, omega
                integral = div((1 - z[0], -z[1]), (horizon * a, horizon * omega))
                naive_force = mul(mul(factor, factor), integral)
                boundary = mul(factor, ((z[0] - 1) / horizon, z[1] / horizon))
                assert add(naive_force, boundary) == (0, 0)
                assert naive_force != (0, 0)
                count += 1
out = {
    "status": "pass",
    "gaussian_rational_substitutions": count,
    "identity": "Fomega=(a+iomega)^2 Xomega + ([v exp(-iomega t)] "
    "+(2a+iomega)[x exp(-iomega t)])/T",
    "negative": "Free decay x=exp(-a t), forcing0: naive inverse-transfer "
    "demodulation is nonzero, corrected demodulation iszero.",
    "boundary": "Integration-by-parts hand derivation plus exact algebra checks; "
    "no endpoint-state sensor, uncertain-a interface, or kernel proof supplied.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
