"""Exact polynomial-kernel enclosure for a declared quintic reference probe."""

import json
from fractions import Fraction as F
from math import ceil, comb, factorial, isqrt
from pathlib import Path


def peak_bounds(coeff, eps, depth=6):
    degree = len(coeff) - 1
    bernstein = [
        sum((coeff[i] * F(comb(k, i), comb(degree, i)) for i in range(k + 1)), F(0))
        for k in range(degree + 1)
    ]
    pieces = [bernstein]
    for _ in range(depth):
        children = []
        for piece in pieces:
            work = piece
            left, right = [work[0]], [work[-1]]
            while len(work) > 1:
                work = [(x + y) / 2 for x, y in zip(work, work[1:], strict=False)]
                left.append(work[0])
                right.append(work[-1])
            children.extend([left, list(reversed(right))])
        pieces = children
    lower = max(abs(p[0]) for p in pieces)
    lower = max(lower, abs(pieces[-1][-1]))
    upper = max(abs(x) for p in pieces for x in p)
    return max(F(0), lower - eps), upper + eps


def response(r, sigma, T, N=60):
    # s=t/T; unit displacement Q=10s³-15s⁴+6s⁵, with zero initial errors.
    a, b, c = F(3, 2) * r * T, 6 * r * sigma * T**2, 8 * r * sigma**2 * T**3
    coeff = [F(0)] * (N + 4)
    v = [F(0), F(0), F(1)]  # M^n b / n!
    for n in range(N + 1):
        for k, jk in enumerate([60, -360, 360]):
            multiplier = F(factorial(k), 1)
            for j in range(n + 1, n + k + 2):
                multiplier /= j
            coeff[n + k + 1] += v[0] * jk * multiplier
        mv = [v[1], v[2], -c * v[0] - b * v[1] - a * v[2]]
        v = [x / (n + 1) for x in mv]
    # Infinity matrix norm; exp(K)<=3^ceil(K), since e<3.
    K = max(F(1), a + b + c)
    eps = F(60 * 3 ** ceil(K)) * K ** (N + 1) / (factorial(N + 1) * (N + 2))
    integral = sum(
        (x * y / (i + j + 1) for i, x in enumerate(coeff) for j, y in enumerate(coeff)), F(0)
    )
    norm_bound = sum(abs(x) for x in coeff)
    error_bound = eps * (2 * norm_bound + eps)
    assert integral > error_bound
    # Low-order coefficients in normalized s agree with the analytic expansion.
    assert coeff[3] == 10
    assert coeff[4] == -15 - F(15, 4) * r * T
    assert coeff[5] == 6 + F(9, 2) * r * T + (F(9, 8) * r**2 - 3 * r * sigma) * T**2
    peaklo, peakhi = peak_bounds(coeff, eps)
    return {
        "peak_abs_lower": peaklo,
        "peak_abs_upper": peakhi,
        "rho": r / sigma,
        "T": T,
        "kernel_degree": N,
        "position_uniform_error_bound": eps,
        "squared_L2_lower": integral - error_bound,
        "squared_L2_upper": integral + error_bound,
        "squared_L2_midpoint": float(integral),
        "squared_L2_interval_width": float(2 * error_bound),
        "first_coefficients": coeff[3:8],
    }


def sqrt_bounds(x, scale=10**12):
    k = isqrt(x.numerator * scale**2 // x.denominator)
    assert F(k, scale) ** 2 <= x < F(k + 1, scale) ** 2
    return F(k, scale), F(k + 1, scale)


def serialize(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, list):
        return [serialize(v) for v in x]
    if isinstance(x, dict):
        return {k: serialize(v) for k, v in x.items()}
    return x


def main():
    results = []
    for T in [F(2, 25), F(1, 4)]:
        endpoints = [response(F(r), F(1), T) for r in [8, 12]]
        A0 = sqrt_bounds(endpoints[0]["squared_L2_lower"])[0]
        A1 = sqrt_bounds(endpoints[0]["squared_L2_upper"])[1]
        B0 = sqrt_bounds(endpoints[1]["squared_L2_lower"])[0]
        B1 = sqrt_bounds(endpoints[1]["squared_L2_upper"])[1]
        klo = (A0 + B1) / (8 * A0 + 12 * B1)
        khi = (A1 + B0) / (8 * A1 + 12 * B0)
        peakA0, peakA1 = endpoints[0]["peak_abs_lower"], endpoints[0]["peak_abs_upper"]
        peakB0, peakB1 = endpoints[1]["peak_abs_lower"], endpoints[1]["peak_abs_upper"]
        pklo = (peakA0 + peakB1) / (8 * peakA0 + 12 * peakB1)
        pkhi = (peakA1 + peakB0) / (8 * peakA1 + 12 * peakB0)
        peak_metrics = {}
        metrics = {}
        for name, k in [("zero", F(0)), ("nominal", F(1, 10)), ("cube", F(5, 48))]:
            lo = max(
                (r * k - 1) ** 2 * row["squared_L2_lower"]
                for r, row in zip([8, 12], endpoints, strict=True)
            )
            hi = max(
                (r * k - 1) ** 2 * row["squared_L2_upper"]
                for r, row in zip([8, 12], endpoints, strict=True)
            )
            peak_metrics[name] = [
                max(
                    abs(r * k - 1) * row["peak_abs_lower"]
                    for r, row in zip([8, 12], endpoints, strict=True)
                ),
                max(
                    abs(r * k - 1) * row["peak_abs_upper"]
                    for r, row in zip([8, 12], endpoints, strict=True)
                ),
            ]
            metrics[name] = {
                "worst_squared_L2_lower": lo,
                "worst_squared_L2_upper": hi,
                "display_interval": [float(lo), float(hi)],
            }
        assert F(1, 12) < klo < khi < F(1, 8)
        results.append(
            {
                "T": T,
                "motion_peak_optimal_interval": [pklo, pkhi],
                "motion_peak_optimal_display": [float(pklo), float(pkhi)],
                "motion_peak_three_coefficients": peak_metrics,
                "endpoint_responses": endpoints,
                "two_rate_L2_optimal_coefficient_interval": [klo, khi],
                "optimal_display": [float(klo), float(khi)],
                "three_coefficients": metrics,
            }
        )
    result = {
        "reference": "q=D*(10s^3-15s^4+6s^5), s=t/T, 0<=s<=1",
        "assumptions": "sigma=1, constant rate either8or12, w=0, zero initial tracking error",
        "objective": "max over TWO rates of integral_0^1(e/D)^2 ds; not continuum or varying rate minimax",
        "results": results,
    }
    Path(__file__).with_name("domain_response_results.json").write_text(
        json.dumps(serialize(result), indent=2) + "\n"
    )
    for row in results:
        print(
            "T",
            row["T"],
            "L2optimal",
            row["optimal_display"],
            "peakoptimal",
            row["motion_peak_optimal_display"],
        )
        print(
            "peak",
            {k: [float(x) for x in v] for k, v in row["motion_peak_three_coefficients"].items()},
        )
        print({k: v["display_interval"] for k, v in row["three_coefficients"].items()})


if __name__ == "__main__":
    main()
