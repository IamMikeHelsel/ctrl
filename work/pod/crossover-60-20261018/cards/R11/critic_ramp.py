"""Independent exact LDL consumer for PM's delayed smooth-reference certificate."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def ldlt(a):
    n = len(a)
    assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
    lower = [[F(i == j) for j in range(n)] for i in range(n)]
    diag = []
    for i in range(n):
        d = a[i][i] - sum(lower[i][k] ** 2 * diag[k] for k in range(i))
        assert d > 0
        diag.append(d)
        for j in range(i + 1, n):
            lower[j][i] = (a[j][i] - sum(lower[j][k] * lower[i][k] * diag[k] for k in range(i))) / d
    assert all(
        sum(lower[i][k] * diag[k] * lower[j][k] for k in range(n)) == a[i][j]
        for i in range(n)
        for j in range(n)
    )
    return diag


def verify(data):
    A = [[F(x) for x in row] for row in data["A"]]
    P = [[F(x) for x in row] for row in data["P"]]
    assert A == [[1, -F(1, 10), -F(1, 10)], [1, 0, 0], [0, 1, 0]]
    assert all(
        P[i][j] - sum(A[k][i] * P[k][l] * A[l][j] for k in range(3) for l in range(3))
        == int(i == j)
        for i in range(3)
        for j in range(3)
    )
    lower = ldlt([[P[i][j] - F(1, 2) * int(i == j) for j in range(3)] for i in range(3)])
    upper = ldlt([[20 * int(i == j) - P[i][j] for j in range(3)] for i in range(3)])
    state = list(map(F, data["initial_state"]))
    assert state == [F(1, 10000)] * 3

    def energy(s):
        return sum(s[i] * P[i][j] * s[j] for i in range(3) for j in range(3))

    assert energy(state) == F(data["initial_energy"]) <= F(1, 2) * F(1, 1000) ** 2
    for n, row in enumerate(data["trace"]):
        old, new = -10 * state[2], -10 * state[1]
        assert row["n"] == n and F(row["position"]) == state[0]
        assert (F(row["v_old"]), F(row["v_new"]), F(row["accel"])) == (old, new, 50 * (new - old))
        assert F(row["energy"]) == energy(state)
        nxt = [state[0] + F(1, 100) * (old + new), state[0], state[1]]
        assert energy(nxt) == energy(state) - sum(x * x for x in state)
        assert energy(nxt) <= F(19, 20) * energy(state)
        state = nxt
    return lower, upper


def main():
    data = json.loads((HERE / "pm_ramp.json").read_text())
    lo, hi = verify(data)
    negatives = []
    for name in (
        "P_coefficient",
        "A_delay_coefficient",
        "initial_history",
        "ramp_endpoint_velocity",
    ):
        d = copy.deepcopy(data)
        if name == "P_coefficient":
            d["P"][0][0] = str(F(d["P"][0][0]) + F(1, 1000))
        elif name == "A_delay_coefficient":
            d["A"][0][2] = "0"
        elif name == "initial_history":
            d["initial_state"][2] = "0"
        else:
            d["trace"][0]["v_old"] = "0"
        try:
            verify(d)
        except AssertionError:
            negatives.append(name)
        else:
            raise AssertionError(name)
    out = {
        "certificate": "P−AᵀPA=I exactly; P−.5I and20I−P exactpositiveLDL",
        "lower_LDL_diagonal": list(map(str, lo)),
        "upper_LDL_diagonal": list(map(str, hi)),
        "trace_rows_checked": len(data["trace"]),
        "semantic_mutations_rejected": negatives,
        "handoff_required_velocity": "-1/1000",
        "scope": "Nominal reference controller with stated delayedsamples; measuredinnererror andtargetchanges not included.",
    }
    (HERE / "critic_ramp.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
