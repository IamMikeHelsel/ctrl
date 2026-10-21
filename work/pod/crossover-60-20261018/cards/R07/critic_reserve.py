"""Independent bounded-state, bounded-delay braking reserve (paired toy state)."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent


def main():
    corners = []
    for q, v, d in itertools.product(
        [F(17, 100), F(18, 100)], [F(0), F(19, 100), F(1, 5)], [F(0), F(1, 20)]
    ):
        stop = q + v * d + 5 * v * v
        T = 10 * v
        assert F(17, 100) <= stop <= F(39, 100)
        assert 0 <= T <= 2
        corners.append(
            {
                "q0": str(q),
                "v0": str(v),
                "delay": str(d),
                "brake_duration": str(T),
                "q_stop": str(stop),
            }
        )
    assert max(F(x["q_stop"]) for x in corners) == F(39, 100)
    # Fixed2s brake is not a robust terminal hold for the whole velocity interval.
    q, v, d = F(17, 100), F(19, 100), F(0)
    finalv = v - F(1, 10) * 2
    finalq = q + 2 * v - F(1, 20) * 4
    assert finalv == F(-1, 100) and finalq == F(7, 20)
    after150 = finalq + 150 * finalv
    assert after150 == F(-23, 20) < -1
    out = {
        "corners": corners,
        "continuous_parameter_bound": "q_stop=q0+v0*d+5*v0² is monotone in q0,v0,d on the declared nonnegative intervals; corner maximum.39 therefore bounds every parameter value, not just samples.",
        "continuous_time_bound": "Coast then brake until actual v0/.1; velocity remains nonnegative through stop, hence q1 ranges betweenq0 andq_stop and holds thereafter.",
        "task_binding": "q2=-q1,v2=-v1; exact paired acceleration and modelMdiag(1,2), torque(-.1,.2), then0.",
        "position_margin": "1/100",
        "halfspace_margin": "1/50",
        "fixed_duration_negative": {
            "final_velocity": str(finalv),
            "q_after150_seconds_unforced": str(after150),
        },
        "unresolved": "Exact-state-dependent timing or certified stopping event must be supplied. Arbitrary independent disturbances, sensor errors, coupled robot physics and self-collision remain outside this toy.",
    }
    (P / "critic_reserve.json").write_text(json.dumps(out, indent=2) + "\n")
    print("All12 reserve edge cases and fixed-duration failure verified")


if __name__ == "__main__":
    main()
