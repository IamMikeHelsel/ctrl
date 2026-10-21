"""Independent consumer for serialized width certificates, including model binding."""

import json
from copy import deepcopy
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent


def point(events, t, k):
    return sum(
        d * c * max(t - tau - i * h, F(0)) ** (4 - k) / factorial(4 - k) / h**4
        for tau, d, h in events
        for i, c in enumerate([1, -4, 6, -4, 1])
    )


def verify(case):
    es = [tuple(map(F, row)) for row in case["events"]]
    assert es[0] == (F(11, 50), F(1, 50), F(1, 5))
    assert es[1][0] == F(13, 25)
    assert es[1][1] in [-F(1, 50), -F(1, 25)]
    assert all(h > 0 for _, _, h in es)
    required = {F(0), F(5, 2)} | {t + i * h for t, _, h in es for i in range(5)}
    certs = case["piece_certificates"]
    knots = [F(c["start"]) for c in certs] + [F(certs[-1]["end"])]
    assert knots == sorted(set(knots))
    assert knots[0] == 0 and knots[-1] == F(5, 2) and required <= set(knots)
    max_a = max_j = max_v = F(0)
    for index, c in enumerate(certs):
        left, right = F(c["start"]), F(c["end"])
        assert (left, right) == (knots[index], knots[index + 1])
        ds = list(map(F, c["derivatives"]))
        width = right - left
        # Five points determine the degree-four polynomial on this known knot-free interval.
        for n in range(5):
            z = width * F(n, 4)
            assert sum(ds[k] * z**k / factorial(k) for k in range(5)) == point(es, left + z, 0)
        b = list(map(F, c["velocity_bernstein"]))
        assert len(b) == 4
        for n in range(4):
            u = F(n, 3)
            bern = sum(b[i] * comb(3, i) * u**i * (1 - u) ** (3 - i) for i in range(4))
            assert bern == sum(ds[k + 1] * (width * u) ** k / factorial(k) for k in range(4))
        max_v = max(max_v, *map(abs, b))
        roots = [F(0), width]
        if ds[4] and 0 < -ds[3] / ds[4] < width:
            roots.append(-ds[3] / ds[4])
        assert set(map(F, c["acceleration_extremum_offsets"])) == set(roots)
        max_a = max(max_a, *(abs(ds[2] + ds[3] * z + ds[4] * z * z / 2) for z in roots))
        max_j = max(max_j, abs(ds[3]), abs(ds[3] + ds[4] * width))
    assert max_a == abs(F(case["acceleration_exact_peak"][1]))
    assert max_j == abs(F(case["jerk_exact_peak"][1]))
    assert max_v == F(case["velocity_sufficient_bound"])
    for order in range(4):
        assert point(es, F(case["deadline"]), order) == F(
            case["deadline_reference_state_q_v_a_j"][order]
        )
    assert F(case["final_tail"]) == max(t + 4 * h for t, _, h in es)
    return {
        "name": case["name"],
        "max_A": str(max_a),
        "max_J": str(max_j),
        "velocity_Bernstein_bound": str(max_v),
    }


cases = json.loads((HERE / "inventor_width.json").read_text())["cases"]
result = {"verified": [verify(c) for c in cases], "mutations_rejected": []}
for mutation in ["old_width", "coefficient", "missing_piece", "bernstein"]:
    c = deepcopy(cases[1])
    if mutation == "old_width":
        c["events"][0][2] = "1/4"
    elif mutation == "coefficient":
        c["piece_certificates"][4]["derivatives"][2] = "0"
    elif mutation == "missing_piece":
        c["piece_certificates"].pop(3)
    else:
        c["piece_certificates"][4]["velocity_bernstein"][2] = "0"
    try:
        verify(c)
    except AssertionError:
        result["mutations_rejected"].append(mutation)
    else:
        raise AssertionError("mutation accepted: " + mutation)
(HERE / "critic_certificate.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
