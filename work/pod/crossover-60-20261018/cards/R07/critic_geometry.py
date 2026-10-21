"""Independent rational reconstruction of curved-fiber producer records."""

import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent


def curve(z, side, T):
    D = 1 + z * z
    q = [side * (1 - z * z) / D, 2 * z / D]
    v = [side * (-4 * z) / D**2 * (2 / T), 2 * (1 - z * z) / D**2 * (2 / T)]
    a = [side * (-4 + 12 * z * z) / D**3 * (2 / T) ** 2, 4 * z * (z * z - 3) / D**3 * (2 / T) ** 2]
    return q, v, a


def main():
    cert = json.loads((P / "inventor_geometry.json").read_text())
    for row in cert["rows"]:
        z = F(row["t"])
        side = F(row["side"])
        T = F(4)
        q, v, a = curve(z, side, T)
        assert q == list(map(F, row["q"]))
        assert sum(x * x for x in q) == 1
        assert (
            sum(x * x for x in v)
            == F(row["velocity_norm_squared_T4"])
            == 16 / (T * T * (1 + z * z) ** 2)
        )
        assert (
            sum(x * x for x in a)
            == F(row["acceleration_norm_squared_T4"])
            == 256 / (T**4 * (1 + z * z) ** 3)
        )
        assert sum(q[i] * v[i] for i in range(2)) == 0
        assert sum(v[i] * v[i] + q[i] * a[i] for i in range(2)) == 0
    q, v, a = curve(F(0), F(-1), F(3))
    assert sum(x * x for x in v) == F(16, 9) > 1
    start = curve(F(-1), F(-1), F(4))
    end = curve(F(1), F(-1), F(4))
    assert start[1] == [F(-1, 2), 0] and end[1] == [F(1, 2), 0]
    # Truncated geometry projection with zero acceleration cannot follow the circle.
    assert start[1] != [0, 0]
    # Validate identities on a separate complete rational probe grid as arithmetic
    # regression, while all-real bounds rely on the displayed rational identities.
    for k in range(-100, 101):
        z = F(k, 100)
        q, v, a = curve(z, F(-1), F(4))
        assert q[0] <= 0 and sum(x * x for x in q) == 1
        assert sum(x * x for x in v) <= 1 and sum(x * x for x in a) <= 1
    result = {
        "producer_rows_independently_checked": len(cert["rows"]),
        "additional_rational_probes": 201,
        "all_time_hand_bridge": "For |z|<=1, left q1<=0; exact norm identities and1+z²>=1 give speed<=1 and ideal acceleration<=1 atT4.",
        "retained_state_boundary": "Initial velocity(-1/2,0), final(+1/2,0); cannot splice to/from rest without altering trajectory or impulsive acceleration.",
        "acceleration_scope": "Ideal Euclidean coordinate acceleration, not torque on a coupled arm.",
        "T3_speed_squared": "16/9",
        "producer_imports": False,
    }
    (P / "critic_geometry.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Curved-fiber source rows independently reconstructed")


if __name__ == "__main__":
    main()
