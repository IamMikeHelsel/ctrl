"""Exact nonorthogonal congruence check for the diagonalizable rank formula."""

import json
from pathlib import Path

from domain_exact import audit, blocks, identity, inverse, mul, transpose


def main():
    p = identity()
    p[0][2] = 2
    p[3][5] = 1
    pinv = inverse(p)
    cases = []
    for weights, expected_rank in [([1, 2, 3], 12), ([1, 1, 2], 8), ([1, 1, 1], 0)]:
        k0 = blocks(weights)
        y0 = k0
        # T'=Y'K'=P(Y0 K0)P^-1. This is not an orthogonal change of coordinates.
        k = mul(mul(transpose(pinv), k0), pinv)
        y = mul(mul(p, y0), transpose(p))
        assert mul(y, k) == mul(mul(p, mul(y0, k0)), pinv)
        row = audit(f"nonorthogonal_rank_{expected_rank}", k, y)
        assert row["phi_rank"] == expected_rank
        row["norms_not_invariant"] = row["K_frobenius_squared"] != row["Y_frobenius_squared"]
        cases.append(row)
    path = Path(__file__).with_name("domain_rank_transport_results.json")
    path.write_text(json.dumps(cases, indent=2, default=str) + "\n")
    for row in cases:
        print(
            row["name"],
            row["phi_rank"],
            "qK",
            row["K_frobenius_squared"],
            "qY",
            row["Y_frobenius_squared"],
        )


if __name__ == "__main__":
    main()
