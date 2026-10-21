"""Exact realification of a complex source-typed toy; no producer imports."""

import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent


def mul(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def add(a, b):
    return [[x + y for x, y in zip(aa, bb, strict=True)] for aa, bb in zip(a, b, strict=True)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def transpose(a):
    return list(map(list, zip(*a, strict=True)))


def realify(a, b):
    return [a[i] + [-v for v in b[i]] for i in range(2)] + [b[i] + a[i] for i in range(2)]


zero2 = [[0, 0], [0, 0]]
i2 = [[1, 0], [0, 1]]
k2 = [[1, 0], [0, -1]]
w2 = [[0, 1], [-1, 0]]
I = realify(i2, zero2)
K = realify(k2, zero2)
W = realify(w2, zero2)
G = realify(zero2, k2)  # Gamma=iK: negative square, negative K-adjoint.
zero = scale(0, I)
assert mul(G, G) == scale(-1, I)
assert mul(transpose(G), K) == scale(-1, mul(K, G))
assert mul(W, G) == scale(-1, mul(G, W))
assert mul(mul(transpose(G), K), G) == K
rows = []
for t in [Q(-15, 8), Q(0), Q(15, 8), Q(40, 9)]:
    H = mul(K, add(I, scale(t, W)))
    residual = add(mul(H, G), mul(transpose(G), H))
    assert residual == scale(2 * t, mul(mul(K, W), G))
    assert (residual == zero) == (t == 0)
    assert mul(mul(transpose(G), H), G) == mul(K, add(I, scale(-t, W)))
    rows.append({"t": str(t), "fixed_gamma_adjoint_residual_zero": residual == zero})
a, b = Q(5, 4), Q(3, 4)
S = add(scale(a, I), scale(b, W))
Si = scale(1 / (a * a + b * b), add(scale(a, I), scale(-b, W)))
H = mul(mul(transpose(S), K), S)
Gn = mul(mul(Si, G), S)
assert mul(Gn, Gn) == scale(-1, I)
assert add(mul(H, Gn), mul(transpose(Gn), H)) == zero
assert add(mul(K, Gn), mul(transpose(Gn), K)) != zero
# Active right gauge: epsilon changes; fixed bare Phi is dressed, not separately moved.
eps = S
epsi = Si
h = G
hi = scale(-1, G)
phi = K
old = mul(mul(epsi, phi), eps)
new_eps = mul(eps, h)
new_inverse = mul(hi, epsi)
new = mul(mul(new_inverse, phi), new_eps)
assert new == mul(mul(hi, old), h)
assert new != old
result = {
    "source_typed_complex_toy": rows,
    "transported_gamma_adjoint": "accepted",
    "wrong_frozen_K_after_passive_transport": "rejected",
    "active_epsilon_right_action": "covariant with bare Phi fixed",
    "scope": "Realification preserves exact complex adjoints. This is a 2D diagnostic, not an actual128-dimensional GU representation; source code bridge is separate.",
}
(HERE / "critic_adjoint.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
