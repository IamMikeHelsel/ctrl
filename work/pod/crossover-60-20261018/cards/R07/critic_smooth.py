"""Independent derivative reconstruction for the rest-to-rest curved toy."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent


def main():
    c = json.loads((P / "inventor_smooth.json").read_text())
    T = F(c["contract"]["duration"])
    assert T == 12
    for row in c["rational_nodes_are_checks_not_alltime_proof"]:
        z = F(row["z"])
        p = 2 * (10 * z**3 - 15 * z**4 + 6 * z**5) - 1
        dp = 60 * z * z * (1 - z) ** 2 / T
        ddp = 120 * z * (1 - z) * (1 - 2 * z) / (T * T)
        D = 1 + p * p
        q = [-(1 - p * p) / D, 2 * p / D]
        dq = [4 * p / D**2, 2 * (1 - p * p) / D**2]
        ddq = [(4 - 12 * p * p) / D**3, 4 * p * (p * p - 3) / D**3]
        v = [x * dp for x in dq]
        a = [ddq[i] * dp * dp + dq[i] * ddp for i in range(2)]
        assert p == F(row["phase"]) and q == list(map(F, row["q"]))
        assert v == list(map(F, row["v"])) and a == list(map(F, row["a"]))
        assert sum(x * x for x in q) == 1 and q[0] <= 0
    vmax = 2 * F(5, 16)
    amax = 4 * F(5, 16) ** 2 + 2 * F(5, 24)
    assert vmax == F(5, 8) and amax == F(155, 192) < 1
    assert F(c["all_time_bounds"]["velocity_norm"]) == vmax
    assert F(c["all_time_bounds"]["acceleration_norm"]) == amax
    # A permitted norm-epsilon tracking perturbation can exit the nominal joint box.
    eps = F(1, 1000)
    nominal = [F(-1), F(0)]
    actual = [-1 - eps, F(0)]
    assert (
        sum((a - b) ** 2 for a, b in zip(actual, nominal, strict=True)) == eps**2 and actual[0] < -1
    )
    out = {
        "exact_derivative_rows_checked": len(c["rational_nodes_are_checks_not_alltime_proof"]),
        "velocity_norm_bound": str(vmax),
        "acceleration_norm_bound": str(amax),
        "rest_join": "qdot and qddot zero at both ends by quintic phase derivatives",
        "all_time_basis": "Pprime=30z²(1-z)²<=15/8, |Psecond|<=15 on[0,1], curve derivative norms<=2,4; chain rule and triangle inequality. This is a hand analytic bridge, not sampling inference.",
        "nominal_margin_negative": {"epsilon": str(eps), "actual_q1": str(actual[0])},
        "scope": "Exact ideal double integrator with acceleration-as-input. No coupled torque, uncertainty, self-collision or feedback guarantee.",
    }
    (P / "critic_smooth.json").write_text(json.dumps(out, indent=2) + "\n")
    print("Rest-to-rest rows and analytic budgets independently checked")


if __name__ == "__main__":
    main()
