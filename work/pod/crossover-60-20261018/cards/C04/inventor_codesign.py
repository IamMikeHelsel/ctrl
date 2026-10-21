"""Fixed-cube gain co-design. Numerical LP proposes; exact vertices accept or reject."""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
R = F(2221, 40000)
KA = F(1, 2)
D = F(1, 100)


def terms(kx, kv, rate):
    b = [-kx + 4 * kv - 16 * KA, -4 * kv + 32 * KA, -16 * KA]
    a = [
        4 - rate + rate * b[0] / 16,
        -12 + 2 * rate + rate * b[1] / 16,
        8 - rate + rate * b[2] / 16,
    ]
    slope = [
        4 * kx - 16 * kv - KA * rate * (b[0] - 16),
        -4 * kx + 32 * kv - KA * rate * (b[1] + 32),
        -16 * kv - KA * rate * (b[2] - 16),
    ]
    return b, a, slope


def expression(vector, kind, rate=F(8), signs=(1, 1, 1)):
    kx, kv, mismatch, slope_bound = vector
    b, a, slope = terms(kx, kv, rate)
    sensor = kx / 1000 + kv / 100 + KA / 20
    if kind == "face":
        return R * (a[0] * signs[0] + a[1] * signs[1] + a[2]) + rate * mismatch / 16
    if kind == "slope":
        return (
            R * sum(x * s for x, s in zip(slope, signs, strict=True))
            + KA * rate * mismatch
            - slope_bound
        )
    if kind == "authority":
        return R * sum(x * s for x, s in zip(b, signs, strict=True)) + sensor + D - 2
    raise ValueError(kind)


def constraints():
    result = []
    for rate in (F(8), F(12)):
        for s1, s2 in product((-1, 1), repeat=2):
            result.append(("face", rate, (s1, s2, 1)))
        for signs in product((-1, 1), repeat=3):
            result.append(("slope", rate, signs))
    result.extend(("authority", F(8), signs) for signs in product((-1, 1), repeat=3))
    return result


def verify(candidate, age):
    kx, kv, mismatch, slope_bound = candidate
    sensor = kx / 1000 + kv / 100 + KA / 20
    values = [(args, expression(candidate, *args)) for args in constraints()]
    age_margin = mismatch - sensor - D - age * slope_bound
    return {
        "kx": str(kx),
        "kv": str(kv),
        "ka": str(KA),
        "mismatch_budget": str(mismatch),
        "slope_bound": str(slope_bound),
        "sensor_cost": str(sensor),
        "age": str(age),
        "age_margin": str(age_margin),
        "face_max": str(max(v for (kind, _, _), v in values if kind == "face")),
        "slope_constraint_max": str(max(v for (kind, _, _), v in values if kind == "slope")),
        "authority_constraint_max": str(
            max(v for (kind, _, _), v in values if kind == "authority")
        ),
        "accepted_by_exact_vertex_check": min(candidate) >= 0
        and max(v for _, v in values) <= 0
        and age_margin >= 0,
        "constraint_count": len(values),
    }


def main():
    zero = [F(0)] * 4
    matrix, rhs = [], []
    for args in constraints():
        constant = expression(zero, *args)
        row = []
        for i in range(4):
            basis = zero.copy()
            basis[i] = F(1)
            row.append(expression(basis, *args) - constant)
        matrix.append([float(x) for x in row])
        rhs.append(float(-constant))
    proposals = []
    for age in (F(1, 100), F(1, 50), F(3, 100), F(1, 25), F(1, 20)):
        optimum = linprog(
            [0.001, 0.01, -1, float(age)],
            A_ub=matrix,
            b_ub=rhs,
            bounds=[(0, None)] * 4,
            method="highs",
        )
        if optimum.success:
            rational = [F(float(x)).limit_denominator(10**8) for x in optimum.x]
            record = verify(rational, age)
            record["numeric_objective"] = float(optimum.fun)
            proposals.append(record)
        else:
            proposals.append({"age": str(age), "solver_status": optimum.message})
    baseline_w = 8 * R / 3
    baseline_slope = max(96 * R + 4 * baseline_w, 80 * R + 6 * baseline_w)
    result = {
        "scope": "Algebraic robust cube and conditional age certificates only. Fixed z transform, same R and center. New gains explicitly change controller. No digital bootstrap/existence/clearance theorem.",
        "radius": str(R),
        "physical_error": str(D),
        "acceleration_gain_fixed": str(KA),
        "baseline_sharp_mismatch": str(baseline_w),
        "baseline_sharp_slope": str(baseline_slope),
        "baseline_conditional_age_ceiling": str((baseline_w - F(93, 1000) - D) / baseline_slope),
        "proposals": proposals,
    }
    (HERE / "inventor_codesign.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
