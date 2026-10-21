"""Independent exact scalar-kernel reconstruction of the declared L2 extension."""

import json
from fractions import Fraction as F
from math import ceil, comb, factorial, isqrt
from pathlib import Path

HERE = Path(__file__).parent
source = json.loads((HERE / "domain_response_results.json").read_text())
checks = []
for row in source["results"]:
    T = F(row["T"])
    for entry in row["endpoint_responses"]:
        r = F(entry["rho"])
        a, b, c = F(3, 2) * r * T, 6 * r * T * T, 8 * r * T**3
        # Kernel g solves g'''+ag''+bg'+cg=0, g(0)=g'(0)=0,g''(0)=1.
        g = [F(0), F(0), F(1, 2)]
        for n in range(58):
            g.append(
                -(a * (n + 2) * (n + 1) * g[n + 2] + b * (n + 1) * g[n + 1] + c * g[n])
                / ((n + 3) * (n + 2) * (n + 1))
            )
        f = [F(0)] * 64
        for n, gn in enumerate(g):
            for m, jm in enumerate([60, -360, 360]):
                f[n + m + 1] += gn * jm * F(factorial(n) * factorial(m), factorial(n + m + 1))
        K = max(F(1), a + b + c)
        eps = 60 * 3 ** ceil(K) * K**61 / F(factorial(61) * 62)
        integral = sum(
            (u * v / F(i + j + 1) for i, u in enumerate(f) for j, v in enumerate(f)), F(0)
        )
        err = eps * (2 * sum(map(abs, f)) + eps)
        assert integral - err == F(entry["squared_L2_lower"])
        assert integral + err == F(entry["squared_L2_upper"])
        assert eps == F(entry["position_uniform_error_bound"])
        assert f[3:8] == list(map(F, entry["first_coefficients"]))

        # Independent endpoint evaluations and local power-to-Bernstein transforms.
        def horner(x, f=f):
            value = F(0)
            for coefficient in reversed(f):
                value = value * x + coefficient
            return value

        peak_lower = max(abs(horner(F(k, 64))) for k in range(65)) - eps
        assert max(F(0), peak_lower) == F(entry["peak_abs_lower"])
        controls = []
        for interval in range(64):
            x = F(interval, 64)
            # Taylor coefficients of p(x+s/64), without de Casteljau subdivision.
            shifted = [
                sum((f[i] * comb(i, k) * x ** (i - k) for i in range(k, 64)), F(0)) / 64**k
                for k in range(64)
            ]
            controls.extend(
                sum((shifted[i] * F(comb(k, i), comb(63, i)) for i in range(k + 1)), F(0))
                for k in range(64)
            )
        assert max(map(abs, controls)) + eps == F(entry["peak_abs_upper"])
        # Norm bound Q''' in [0,1]: quadratic min -30 at .5, endpoints60.
        assert 60 - 360 * F(1, 2) + 360 * F(1, 2) ** 2 == -30
        checks.append(
            {"T": str(T), "r": str(r), "integral": float(integral), "width": float(2 * err)}
        )
    A, B = row["endpoint_responses"]

    def sqrtlo(x):
        x = F(x)
        scale = 10**12
        return F(isqrt(x.numerator * scale**2 // x.denominator), scale)

    A0 = sqrtlo(A["squared_L2_lower"])
    A1 = sqrtlo(A["squared_L2_upper"]) + F(1, 10**12)
    B0 = sqrtlo(B["squared_L2_lower"])
    B1 = sqrtlo(B["squared_L2_upper"]) + F(1, 10**12)
    bounds = [(A0 + B1) / (8 * A0 + 12 * B1), (A1 + B0) / (8 * A1 + 12 * B0)]
    assert bounds == list(map(F, row["two_rate_L2_optimal_coefficient_interval"]))
# Negative objective binding: two rates and quintic L2 cannot be original 7-stage peak game.
assert source["objective"].startswith("max over TWO rates of integral")
(HERE / "critic_kernel.json").write_text(
    json.dumps(
        {
            "exact_reconstruction": checks,
            "limits": "Exact rational arithmetic conditional on analytical Taylor remainder derivation. Changed quintic reference, two rates, no disturbance, L2 objective; not the original source peak problem.",
        },
        indent=2,
    )
    + "\n"
)
print(json.dumps(checks, indent=2))
