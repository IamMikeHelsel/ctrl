"""Independent exact consumer of a declared 2D diagnostic, not a GU action proof."""

import copy
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
I = ((Q(1), Q(0)), (Q(0), Q(1)))
K = ((Q(1), Q(0)), (Q(0), Q(-1)))
W = ((Q(0), Q(1)), (Q(-1), Q(0)))
ZERO = ((Q(0), Q(0)), (Q(0), Q(0)))


def m(v):
    return tuple(tuple(Q(x) for x in row) for row in v)


def product(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0])))
        for i in range(len(a))
    )


def adj(a):
    # All entries of this diagnostic are real; this is its complex adjoint.
    return tuple(zip(*a, strict=True))


def plus(a, b):
    return tuple(tuple(a[i][j] + b[i][j] for j in range(len(a[0]))) for i in range(len(a)))


def times(c, a):
    return tuple(tuple(c * x for x in row) for row in a)


def sandwich(p, h):
    return product(product(adj(p), h), p)[0][0]


def consumer(receipt):
    s, si, h = (m(receipt[key]) for key in ("S", "S_inverse", "H"))
    gamma, gamma_new = (m(receipt[key]) for key in ("old_gamma", "new_gamma"))
    psi, psi_new = (m(receipt[key]) for key in ("old_field", "new_field"))
    sp, a, hp = (m(receipt[key]) for key in ("S_derivative", "induced_connection", "H_derivative"))
    assert product(s, si) == product(si, s) == I
    assert h == product(product(adj(s), K), s)
    assert h == product(K, plus(I, times(Q(receipt["t"]), W)))
    assert gamma_new == product(product(si, gamma), s)
    assert psi_new == product(si, psi)
    assert product(adj(gamma_new), h) == product(h, gamma_new)
    assert sandwich(psi_new, h) == sandwich(psi, K) == 3
    assert sandwich(psi_new, product(h, gamma_new)) == 5
    assert a == product(si, sp)
    assert hp == plus(product(adj(a), h), product(h, a))
    assert plus(
        m(receipt["new_constant_field_derivative"]), product(a, product(si, ((Q(1),), (Q(0),))))
    ) == ((0,), (0,))
    return True


payload = json.loads((HERE / "inventor_transport.json").read_text())
assert consumer(payload)
negative = {}
for name, key, value in [
    ("freeze_gamma", "new_gamma", payload["old_gamma"]),
    ("wrong_inverse_as_forward", "S_inverse", payload["S"]),
    ("freeze_field", "new_field", payload["old_field"]),
    ("omit_connection", "induced_connection", ZERO),
    ("freeze_H_derivative", "H_derivative", ZERO),
    ("freeze_metric", "H", K),
    ("wrong_parameter", "t", "1"),
]:
    bad = copy.deepcopy(payload)
    bad[key] = value
    try:
        consumer(bad)
    except AssertionError:
        negative[name] = "rejected"
    else:
        raise AssertionError(name)

s, si, h = (m(payload[key]) for key in ("S", "S_inverse", "H"))
assert product(product(adj(s), K), s) != K  # Passive change is not fixed-K gauge.
assert product(product(adj(K), K), K) == K
assert product(product(adj(K), h), K) == product(K, plus(I, times(-Q(payload["t"]), W)))
# A generic K-unitary does not preserve the one-parameter family pointwise.
g = ((Q(5, 3), Q(4, 3)), (Q(4, 3), Q(5, 3)))
assert product(product(adj(g), K), g) == K
hg = product(product(adj(g), h), g)
relative = plus(product(K, hg), times(-1, I))
assert product(relative, relative) == times(-(Q(payload["t"]) ** 2), I)
assert hg != h and hg != product(K, plus(I, times(-Q(payload["t"]), W)))
# Source-typed generator: negative square and negative K-adjoint. W is K-selfadjoint.
gamma_minus = ((Q(0), Q(1)), (Q(-1), Q(0)))
# This W cannot also serve as a source negative-adjoint gamma; use complex toy separately.
assert product(adj(gamma_minus), K) != times(-1, product(K, gamma_minus))
# Full fixed generator action fails already for gamma=K, whereas all its products transport.
assert product(s, K) != product(K, s)
transported = product(product(si, K), s)
assert product(transported, transported) == I
# All rational hyperbola parameters below obey exact congruence, inverse and fixed-K exclusion.
parameters = []
for z in [Q(-3, 4), Q(-1, 3), Q(0), Q(1, 5), Q(1, 3), Q(3, 4)]:
    a, b = (1 + z * z) / (1 - z * z), 2 * z / (1 - z * z)
    t, norm = 2 * a * b, a * a + b * b
    ss = plus(times(a, I), times(b, W))
    ii = times(1 / norm, plus(times(a, I), times(-b, W)))
    hh = product(K, plus(I, times(t, W)))
    assert product(ii, ss) == I and product(product(adj(ss), K), ss) == hh
    assert (hh == K) == (t == 0)
    parameters.append({"z": str(z), "t": str(t)})
result = {
    "producer_sha256": hashlib.sha256((HERE / "inventor_transport.json").read_bytes()).hexdigest(),
    "independent_receipt": "accepted",
    "semantic_mutations": negative,
    "six_rational_controls": parameters,
    "K_unitary_noncentral_relative_square": str(-(Q(payload["t"]) ** 2)),
    "scope": "2x2 diagnostic only; all-real result requires the separate sqrt proof; no GU action or global bundle equivalence.",
}
(HERE / "critic_transport.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
