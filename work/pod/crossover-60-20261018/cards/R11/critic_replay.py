"""Independent physical held-state enclosure and exact delayed-loop receipt audit."""

import copy
import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCALE = 10**70


def floor(q):
    return q.numerator // q.denominator


def ceil(q):
    return -((-q.numerator) // q.denominator)


def mul(a, b):
    products = [x * y for x in a for y in b]
    return min(products) // SCALE, -((-max(products)) // SCALE)


def delayed_receipt(data):
    assert F(data["H"]) == F(1, 50) and F(data["initial_error"]) == F(1, 1000)
    for name, gain in [("unstable_trace", F(6, 5)), ("stable_trace", F(1, 2))]:
        previous = current = F(1, 1000)
        E0 = current**2 - current * previous + gain * previous**2
        for i, row in enumerate(data[name]):
            assert row["n"] == i and F(row["time"]) == F(i, 50)
            assert F(row["error"]) == current
            assert F(row["speed_command"]) == -50 * gain * previous
            assert (
                F(row["energy"])
                == current**2 - current * previous + gain * previous**2
                == gain**i * E0
            )
            previous, current = current, current - gain * previous
    violations = [r["n"] for r in data["unstable_trace"] if abs(F(r["speed_command"])) > F(1, 10)]
    assert min(violations) == 6
    assert max(abs(F(r["speed_command"])) for r in data["stable_trace"]) == F(1, 40)


def main():
    source = json.loads((HERE / "domain_sampled.json").read_text())
    assert source["parameters"]["initial_q"] == "-1/500"
    x = F(1, 25)
    n = 50
    exp_lower = sum((x**k / math.factorial(k) for k in range(n + 1)), F(0))
    exp_upper = exp_lower + (x ** (n + 1) / math.factorial(n + 1)) / (1 - x / F(n + 2))
    E = (floor(SCALE / exp_upper), ceil(SCALE / exp_lower))
    out = []
    for index, missing in enumerate((0, 1, 2)):
        q = (-SCALE // 500, -SCALE // 500)
        for k in range(80):
            c = F(-k, 1000) + F(missing - 1, 40)
            ci = c * SCALE
            assert ci.denominator == 1
            ci = ci.numerator
            product = mul(E, (q[0] - ci, q[1] - ci))
            q = (ci + product[0], ci + product[1])
        e = (F(q[0], SCALE) + F(82, 1000), F(q[1], SCALE) + F(82, 1000))
        lower, upper = map(F, source["cases"][index]["e_at_80th_release_interval"])
        assert lower <= e[0] <= e[1] <= upper
        out.append(
            {
                "case": source["cases"][index]["case"],
                "direct_physical_error_interval": list(map(str, e)),
                "display_radians": float(sum(e) / 2),
            }
        )
    receipt = json.loads((HERE / "pm_outer.json").read_text())
    delayed_receipt(receipt)
    mutations = []
    for label in ("sample_time", "retained_error", "speed_command", "energy"):
        bad = copy.deepcopy(receipt)
        key = {
            "sample_time": "time",
            "retained_error": "error",
            "speed_command": "speed_command",
            "energy": "energy",
        }[label]
        bad["unstable_trace"][6][key] = str(F(bad["unstable_trace"][6][key]) + F(1, 10000))
        try:
            delayed_receipt(bad)
        except AssertionError:
            mutations.append(label)
        else:
            raise AssertionError(label)
    result = {
        "held_angle_state_replay": out,
        "inner_exponential_method": "positiveexp series plus reciprocal, directed70-digit physical q recurrence; producer uses alternating exp error closed form",
        "outer_receipt": "all200 rows exact match",
        "first_authority_violation_n": 6,
        "first_authority_violation_time": "3/25",
        "stable_100step_speed_max": "1/40",
        "semantic_mutations_rejected": mutations,
        "scope": "Declared toy model and exact retainedstates; no physicalhardwareor arbitrarydelayclaim.",
    }
    (HERE / "critic_replay.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
