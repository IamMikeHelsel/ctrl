"""Independent exact enclosure of a candidate essential-matrix box and ray boxes.

A multi-affine function takes its extrema at box vertices. This is a scoped
candidate rejection, not a completeness proof for all calibrated poses.
"""

import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path


def residual(e, x, y):
    return sum(y[i] * e[i][j] * x[j] for i in range(3) for j in range(3))


def bounds(e, x, y, eps, eta):
    values = []
    # Optimize matrix entries analytically for each ray-box vertex.
    for signs in product((-1, 1), repeat=4):
        xx = [x[0] + signs[0] * eps, x[1] + signs[1] * eps, F(1)]
        yy = [y[0] + signs[2] * eps, y[1] + signs[3] * eps, F(1)]
        mid = residual(e, xx, yy)
        radius = eta * sum(abs(a * b) for a in xx for b in yy)
        values += [mid - radius, mid + radius]
    return min(values), max(values)


def brute(e, x, y, eps, eta):
    values = []
    for signs in product((-1, 1), repeat=4):
        xx = [x[0] + signs[0] * eps, x[1] + signs[1] * eps, F(1)]
        yy = [y[0] + signs[2] * eps, y[1] + signs[3] * eps, F(1)]
        for esigns in product((-1, 1), repeat=9):
            ee = [[e[i][j] + eta * esigns[3 * i + j] for j in range(3)] for i in range(3)]
            values.append(residual(ee, xx, yy))
    return min(values), max(values)


def main():
    e = [[F(0), F(-2), F(0)], [F(2), F(0), F(1)], [F(0), F(1), F(0)]]
    eps = eta = F(1, 100)
    records = []
    for depth in [F(2), F(101, 100), F(3, 2)]:
        v = F(0) if depth == F(3, 2) else F(1, 3)
        x, y = [F(0), v, F(1)], [1 / depth, v, F(1)]
        lo, hi = bounds(e, x, y, eps, eta)
        assert (lo, hi) == brute(e, x, y, eps, eta)
        rejected = lo > 0 or hi < 0
        assert rejected == (depth == 2)
        # Register the matrix gauge: scaling E also scales its entry-error radius.
        for scale in [F(1, 5), F(-3)]:
            scaled = [[scale * value for value in row] for row in e]
            a, b = bounds(scaled, x, y, eps, abs(scale) * eta)
            assert (a, b) == tuple(sorted([scale * lo, scale * hi]))
        records.append(
            {
                "depth": str(depth),
                "v": str(v),
                "lower": str(lo),
                "upper": str(hi),
                "reject_entire_candidate_box": rejected,
            }
        )
    # Soundness failure cases: loosen uncertainty and include original plane.
    x, y = [F(0), F(1, 3), F(1)], [F(1, 2), F(1, 3), F(1)]
    assert bounds(e, x, y, eps, F(1))[0] < 0 < bounds(e, x, y, eps, F(1))[1]
    assert bounds(e, x, [F(1), F(1, 3), F(1)], eps, eta)[0] < 0
    report = {
        "method": "Exact rational multi-affine box extrema; independently exhaustive8192vertices percase",
        "coordinate_error": str(eps),
        "matrix_entry_error": str(eta),
        "cases": records,
        "scope": "Registered E scale, bounded normalized-ray errors and one candidate E box. No complete alternate-pose cover, calibration-error justification, novelty, Lean proof, or robot validation.",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
