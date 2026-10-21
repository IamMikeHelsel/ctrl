"""Exact Q(sqrt2) sharp rest-to-rest snap fixture; analytic bridge is explicit."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


class Q:
    def __init__(self, a=0, b=0):
        self.a = F(a)
        self.b = F(b)

    def __add__(self, o):
        if not isinstance(o, Q):
            o = Q(o)
        return Q(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __sub__(self, o):
        return self + -o if isinstance(o, Q) else self + Q(-o)

    def __rsub__(self, o):
        return Q(o) + -self

    def __mul__(self, o):
        if not isinstance(o, Q):
            o = Q(o)
        return Q(self.a * o.a + 2 * self.b * o.b, self.a * o.b + self.b * o.a)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return self * F(1, o)

    def __pow__(self, n):
        z = Q(1)
        for _ in range(n):
            z = z * self
        return z

    def __eq__(self, o):
        if not isinstance(o, Q):
            o = Q(o)
        return self.a == o.a and self.b == o.b

    def wire(self):
        return [str(self.a), str(self.b)]

    def numeric(self):
        return float(self.a) + 2**0.5 * float(self.b)


a = Q(F(1, 2), F(-1, 4))
ts = [Q(0), a, Q(F(1, 2)), 1 - a, Q(1)]
us = [1, -1, 1, -1]
state = [Q(0)] * 4
rows = []
for l, r, u in zip(ts[:-1], ts[1:], us, strict=True):
    d = r - l
    q, v, ac, j = state
    state = [
        q + v * d + ac * d**2 / 2 + j * d**3 / 6 + u * d**4 / 24,
        v + ac * d + j * d**2 / 2 + u * d**3 / 6,
        ac + j * d + u * d**2 / 2,
        j + u * d,
    ]
    rows.append({"time": r.wire(), "snap": u, "state": [s.wire() for s in state]})
assert state == [Q(F(1, 384)), Q(0), Q(0), Q(0)]


# Moment constraints and L1 dualintegral. P=-x³/6+x²/4−5x/48+1/96.
def prim(x):
    return -(x**4) / 24 + x**3 / 12 - 5 * x**2 / 96 + x / 96


moments = []
for power in range(4):
    val = sum(
        (
            u * (r ** (power + 1) - l ** (power + 1)) / (power + 1)
            for l, r, u in zip(ts[:-1], ts[1:], us, strict=True)
        ),
        Q(),
    )
    moments.append(val)
assert moments[:3] == [Q(0)] * 3 and moments[3] == Q(F(-1, 64))
L1 = sum((u * (prim(r) - prim(l)) for l, r, u in zip(ts[:-1], ts[1:], us, strict=True)), Q())
assert L1 == Q(F(1, 384))
S = F(400)
T = F(1, 10)
endpoint = S * T**4 / F(384)
assert endpoint == F(1, 9600) < F(1, 1000) < S * T**4 / 24
out = {
    "field": "a+b sqrt2",
    "switches": [t.wire() for t in ts],
    "normalized_rows": rows,
    "moments": [x.wire() for x in moments],
    "dual_L1": L1.wire(),
    "physical": {
        "S": str(S),
        "T": str(T),
        "J": "10",
        "sharp_displacement": str(endpoint),
        "marginal_displacement_cap": str(S * T**4 / 24),
        "rejected_request_displacement": "1/1000",
        "max_jerk_exact": (S * T * Q(F(-1, 2), F(1, 2))).wire(),
    },
    "scope": "Rest initial and finalvelocity/acceleration/jerk0, prospective task distinctfromsource. Exact switch trajectory and dual arithmetic; continuousmoment and sign/integral bridges handderived unless separatelyformalized. Snap jumps allowed; no boundedcrackle claim.",
}
(HERE / "pm_snap.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: v for k, v in out.items() if k != "normalized_rows"}, indent=2))
