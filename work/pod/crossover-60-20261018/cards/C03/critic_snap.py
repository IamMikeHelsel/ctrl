"""Independent exact quadratic-field moment and dual check; no producer imports."""

import json
from fractions import Fraction as F
from pathlib import Path


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[0], -x[1]


def mul(x, y):
    return x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def scale(x, k):
    return x[0] * k, x[1] * k


def power(x, n):
    out = (F(1), F(0))
    for _ in range(n):
        out = mul(out, x)
    return out


def integral(poly, a, b):
    total = (F(0), F(0))
    for i, c in enumerate(poly):
        total = add(total, scale(add(power(b, i + 1), neg(power(a, i + 1))), c / F(i + 1)))
    return total


def main():
    zero = (F(0), F(0))
    one = (F(1), F(0))
    a = (F(1, 2), F(-1, 4))
    half = (F(1, 2), F(0))
    b = (F(1, 2), F(1, 4))
    knots = [zero, a, half, b, one]
    signs = [1, -1, 1, -1]
    kernels = [
        [F(1)],
        [F(1), F(-1)],
        [F(1, 2), F(-1), F(1, 2)],
        [F(1, 6), F(-1, 2), F(1, 2), F(-1, 6)],
    ]
    moments = []
    for polynomial in kernels:
        out = zero
        for i, sgn in enumerate(signs):
            out = add(out, scale(integral(polynomial, knots[i], knots[i + 1]), sgn))
        moments.append(out)
    assert moments == [zero, zero, zero, (F(1, 384), F(0))]
    P = [F(1, 96), F(-5, 48), F(1, 4), F(-1, 6)]
    for root in [a, half, b]:
        val = zero
        for i, c in enumerate(P):
            val = add(val, scale(power(root, i), c))
        assert val == zero
    # P=-1/6*(t-a)*(t-.5)*(t-b); ordered roots and leading sign prove cell signs.
    product = [one]
    for root in [a, half, b]:
        out = [zero] * (len(product) + 1)
        for i, c in enumerate(product):
            out[i] = add(out[i], mul(c, neg(root)))
            out[i + 1] = add(out[i + 1], c)
        product = out
    assert [scale(c, F(-1, 6)) for c in product] == [(c, F(0)) for c in P]
    support = zero
    for i, sgn in enumerate(signs):
        support = add(support, scale(integral(P, knots[i], knots[i + 1]), sgn))
    assert support == (F(1, 384), F(0))
    # q kernel differs from P by an exact linear combination of three zero moments.
    lambdas = [F(1, 96), F(-5, 48), F(1, 2)]
    for i in range(4):
        assert kernels[3][i] - P[i] == sum(
            l * (k[i] if i < len(k) else 0) for l, k in zip(lambdas, kernels[:3], strict=True)
        )
    T = F(1, 10)
    S = F(400)
    bound = S * T**4 / 384
    assert bound == F(1, 9600) < F(1, 1000) < S * T**4 / 24
    # Terminal jerk omission invalidates q=integral(P u); u=1 has nonzero moments.
    assert integral(kernels[3], zero, one) != (integral(P, zero, one))
    out = {
        "normalized_moments_j_a_v_q": [[str(v) for v in x] for x in moments],
        "dual_integral_abs": "1/384",
        "dual_coefficients": list(map(str, P)),
        "zero_moment_multipliers": list(map(str, lambdas)),
        "scaled_T": "1/10",
        "scaled_S": "400",
        "sharp_position_bound": "1/9600",
        "rejected_position": "1/1000",
        "componentwise_snap_position_cap": "1/600",
        "jerk_peak": "20*(sqrt(2)-1)<10",
        "negative": "Dropping terminal moments breaks kernel-to-dual identity; constant snap u1 is a direct test.",
        "scope": "Exact field arithmetic and hand integral support proof; no claim about the source stop task or plant.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
