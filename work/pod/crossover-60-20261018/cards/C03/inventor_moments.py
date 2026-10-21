"""Exact normalized full-endpoint admission counterexample and sharp mixed dual."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def integral(coeff, lo, hi):
    return sum((c * (hi ** (i + 1) - lo ** (i + 1)) / (i + 1) for i, c in enumerate(coeff)), F(0))


def multiply(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def endpoint(pieces):
    a = sum((integral(p, lo, hi) for lo, hi, p in pieces), F(0))
    v = sum((integral(multiply(p, [F(1), -F(1)]), lo, hi) for lo, hi, p in pieces), F(0))
    q = sum(
        (integral(multiply(p, [F(1, 2), -F(1), F(1, 2)]), lo, hi) for lo, hi, p in pieces), F(0)
    )
    return [q, v, a, F(0)]


triangle = [(F(0), F(1, 2), [F(0), F(1)]), (F(1, 2), F(1), [F(1), -F(1)])]
# Each requested component is realizable in isolation with j(0)=j(1)=0,
# |j'|<=1 and |j|<=1. They need not share the other endpoint coordinates.
positive_half = [(lo, hi, [c / 2 for c in p]) for lo, hi, p in triangle]
negative_half = [(lo, hi, [-c / 2 for c in p]) for lo, hi, p in triangle]
qa = endpoint(positive_half)
qv = endpoint(negative_half)
assert qa[2] == F(1, 8)
assert qv[1] == -F(1, 16)
sharp = [
    (F(0), F(1, 4), [F(0), -F(1)]),
    (F(1, 4), F(3, 4), [-F(1, 2), F(1)]),
    (F(3, 4), F(1), [F(1), -F(1)]),
]
sharp_state = endpoint(sharp)
assert sharp_state[2] - 2 * sharp_state[1] == F(1, 16)
# K=t-t²; subtract3/16 because integral snap=j(1)-j(0)=0.
polynomial = [-F(3, 16), F(1), -F(1)]
abs_integral = (
    -integral(polynomial, F(0), F(1, 4))
    + integral(polynomial, F(1, 4), F(3, 4))
    - integral(polynomial, F(3, 4), F(1))
)
assert abs_integral == F(1, 16)
# Exact factorization specifies the sign intervals, rather than sampling them.
assert multiply([-F(1, 4), F(1)], [F(3, 4), -F(1)]) == polynomial
request = [F(0), -F(1, 16), F(1, 8), F(0)]
request_support = request[2] - 2 * request[1]
assert request_support == F(1, 4) > abs_integral
out = {
    "scope": "Declared normalized diagnostic, not source stop task: initial state0, T1, S1,J1, finalj0; signed motion allowed.",
    "request_q_v_a_j": list(map(str, request)),
    "individual_a_witness": list(map(str, qa)),
    "individual_v_witness": list(map(str, qv)),
    "individual_q_witness": ["0"] * 4,
    "mixed_dual": {
        "functional": "a(1)-2v(1)",
        "upper_bound": str(abs_integral),
        "requested_value": str(request_support),
        "polynomial": "t-t²-3/16=(t-1/4)(3/4-t)",
        "sharp_snap": "-1,+1,-1 on [0,1/4],[1/4,3/4],[3/4,1]",
        "sharp_endpoint_q_v_a_j": list(map(str, sharp_state)),
        "logic": "Integration by parts plus |snap|<=1 and terminal jerk equality; no optimizer.",
    },
}
(HERE / "inventor_moments.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))

# Same mixed dual with actual source execution history, terminal v=a=j=0.
# Reject a proposed .44s execution horizon without changing source's actual deadline.
a0, v0, j0, S, horizon = F(51, 20), F(2601, 8000), F(10), F(400), F(11, 25)
A, V, dj = -a0, -v0 - a0 * horizon, -j0
mixed = A - 2 * V / horizon - F(3, 16) * horizon * dj
bound = S * horizon**2 / 16
assert mixed == F(8541, 1760) and bound == F(121, 25)
assert mixed - bound == F(113, 8800) > 0
out["source_history_short_horizon_probe"] = {
    "a0_v0_j0": list(map(str, [a0, v0, j0])),
    "execution_horizon": str(horizon),
    "terminal_v_a_j": ["0", "0", "0"],
    "mixed_lhs": str(mixed),
    "upper_bound": str(bound),
    "excess": str(mixed - bound),
    "scope": "Necessary rejection of a hypothetical shorter deadline from the actual execution state; original accepted task horizon249/200 is unchanged.",
}
(HERE / "inventor_moments.json").write_text(json.dumps(out, indent=2) + "\n")

# Resource accounting must propagate the old reference during known latency.
arrival = [F(5, 192), F(5, 16), F(5, 2), F(10)]
ell = F(1, 200)
q0, vv0, aa0, jj0 = arrival
execution = [
    q0 + vv0 * ell + aa0 * ell**2 / 2 + jj0 * ell**3 / 6,
    vv0 + aa0 * ell + jj0 * ell**2 / 2,
    aa0 + jj0 * ell,
    jj0,
]
assert execution == [F(44217, 1600000), F(2601, 8000), F(51, 20), F(10)]
out["latency_retained_history"] = {
    "arrival_q_v_a_j": list(map(str, arrival)),
    "latency": str(ell),
    "execution_q_v_a_j": list(map(str, execution)),
    "negative_control": "Resetting a,v,j to0 makes the tested mixed inequality pass vacuously, but evaluates a different initial-value problem.",
}
(HERE / "inventor_moments.json").write_text(json.dumps(out, indent=2) + "\n")
