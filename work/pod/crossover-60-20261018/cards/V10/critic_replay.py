"""Consume other workers' exact fixtures independently, with semantic corruptions."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def det(r):
    return (
        r[0][0] * (r[1][1] * r[2][2] - r[1][2] * r[2][1])
        - r[0][1] * (r[1][0] * r[2][2] - r[1][2] * r[2][0])
        + r[0][2] * (r[1][0] * r[2][1] - r[1][1] * r[2][0])
    )


def check_rotation(data):
    assert data["known_points"] == [[1, 0, 0], [0, 0, 1]]
    assert data["observations"] == [[0, 0], [0, 0]] and data["camera_center"] == [0, 0, 0]
    rs = []
    for name in ("Rplus", "Rminus"):
        r = [[F(x) for x in row] for row in data[name]]
        assert det(r) == 1
        assert all(
            sum(r[k][i] * r[k][j] for k in range(3)) == int(i == j)
            for i in range(3)
            for j in range(3)
        )
        assert all(r[2][j] > 0 for j in (0, 2))
        assert max(sum((r[i][j] / r[2][j]) ** 2 for i in (0, 1)) for j in (0, 2)) == F(16, 9)
        rs.append(r)
    mean = [[sum(r[i][j] for r in rs) / 2 for j in range(3)] for i in range(3)]
    assert mean == [[F(x) for x in row] for row in data["convex_mean"]]
    assert det(mean) == 0
    assert all(mean[2][j] > 0 and mean[0][j] == mean[1][j] == 0 for j in (0, 2))


def main():
    d = json.loads((HERE / "inventor_rotation.json").read_text())
    check_rotation(d)
    rejected = []
    for label in ("reflection", "wrong_center", "wrong_observation", "false_mean"):
        m = copy.deepcopy(d)
        if label == "reflection":
            m["Rplus"][1][1] = "-1"
        if label == "wrong_center":
            m["camera_center"] = [1, 0, 0]
        if label == "wrong_observation":
            m["observations"][1][0] = 1
        if label == "false_mean":
            m["convex_mean"][0][0] = "1/1000"
        try:
            check_rotation(m)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(label)
    # Independent camera projection of the domain optimal and wrong-norm points.
    for x, expected in ((F(0), F(1, 16)), (F(1, 10), F(29, 400))):
        y, z = F(1, 4), F(1)
        r1 = (x / z, y / z)
        r2 = ((x - 1) / z + 1, y / z - F(1, 2))
        assert max(sum(a * a for a in r) for r in (r1, r2)) == expected
    u, g, M, K, delta = F(9, 8), F(1, 10), F(3, 2), F(8, 5), F(1, 50)
    assert u * u >= F(5, 4) and M * M >= 1 + F(5, 4) and K * K >= 1 + (u + g) ** 2
    k = delta * K
    outer = (g + M * k) / (1 - k)
    assert k < 1 and outer == F(37, 242) < F(1, 4)
    # Same extrinsic t is not the same physical center during rotation perturbation.
    c, s = F(9999, 10001), F(200, 10001)
    assert c * c + s * s == 1 and 2 * (1 - c) <= delta * delta
    # True Rz X+t=e3, X=100e1. Nominal I with unchanged t has large image error.
    nominal = (100 * (1 - c), -100 * s, F(1))
    assert nominal[0] ** 2 + nominal[1] ** 2 > outer**2
    out = {
        "fixed_extrinsic_translation_negative": {
            "nominal_residual_squared": str(nominal[0] ** 2 + nominal[1] ** 2),
            "wrong_outer_threshold": str(outer),
        },
        "producer_rotation_fixture": "exactly independently reconstructed",
        "semantic_mutations_rejected": rejected,
        "domain_fixture_squared_errors": ["1/16", "29/400"],
        "cell_constants": {"k": str(k), "enlarged_threshold": str(outer), "nominal_lower": "1/4"},
        "scope": "Unknown-rotation lower-bound and norm perturbation bridges reviewed by hand; finite exact arithmetic is not a full search coverage certificate.",
    }
    (HERE / "critic_replay.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
