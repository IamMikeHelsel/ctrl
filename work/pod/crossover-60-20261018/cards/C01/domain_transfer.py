"""Exact characteristic and transfer numerators for the augmented frozen controller."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def determinant(matrix):
    out = [F(0)]
    for permutation in itertools.permutations(range(len(matrix))):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(len(matrix))
            for j in range(i + 1, len(matrix))
        )
        term = [F((-1) ** inversions)]
        for i, j in enumerate(permutation):
            term = mul(term, matrix[i][j])
        out = add(out, term)
    return out


def check(rate, lam, kp, kd, ka, k):
    a = [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, -rate, rate], [-lam * kp, -lam * kd, -lam * ka, -lam]]
    pencil = [
        [[F(-a[i][j]), F(1)] if i == j else [F(-a[i][j])] for j in range(4)] for i in range(4)
    ]
    denominator = determinant(pencil)
    expected = [rate * lam * kp, rate * lam * kd, rate * lam * (1 + ka), rate + lam, 1]
    assert denominator == expected
    numerators = []
    for forcing in [[0, 0, rate, 0], [0, 0, -1, lam * k - 1]]:
        bordered = [row + [[-F(b)]] for row, b in zip(pencil, forcing, strict=True)]
        bordered.append([[F(1)], [F(0)], [F(0)], [F(0)], [F(0)]])
        numerators.append(determinant(bordered))
    assert numerators == [[rate * lam, rate], [rate * lam * k - rate - lam, -1]]
    a0, a1, a2, a3, _ = denominator
    routh = a3 * a2 * a1 - a1 * a1 - a3 * a3 * a0
    factored = (
        rate
        * lam
        * (rate * lam * ((rate + lam) * (1 + ka) * kd - kd * kd) - (rate + lam) ** 2 * kp)
    )
    assert routh == factored
    if rate == 80 and kp == 800 and kd == 60 and ka == F(1, 2):
        assert routh == 80 * lam * 6400 * (lam * lam + 25 * lam - 800)
    return {
        "rate": str(rate),
        "lambda": str(lam),
        "kp": str(kp),
        "kd": str(kd),
        "ka": str(ka),
        "feedforward_k": str(k),
        "denominator_ascending": list(map(str, denominator)),
        "disturbance_numerator_ascending": list(map(str, numerators[0])),
        "jerk_numerator_ascending": list(map(str, numerators[1])),
        "routh_final_determinant": str(routh),
        "jerk_dc_gain": str(numerators[1][0] / denominator[0]),
    }


def main():
    rows = []
    for rate in [F(80), F(96), F(120)]:
        for lam in [F(10), F(20), F(40)]:
            for k in [F(1, 96), F(1, 96) + 1 / lam]:
                rows.append(check(rate, lam, F(800), F(60), F(1, 2), k))
    for gains in [(F(200), F(35), F(5, 4)), (F(15625, 64), F(625, 16), F(43, 32))]:
        rows.append(check(F(80), F(20), *gains, F(29, 480)))
    path = Path(__file__).with_name("domain_transfer_results.json")
    path.write_text(json.dumps(rows, indent=2) + "\n")
    print(f"{len(rows)} exact transfer/characteristic checks passed; saved {path}")


if __name__ == "__main__":
    main()
