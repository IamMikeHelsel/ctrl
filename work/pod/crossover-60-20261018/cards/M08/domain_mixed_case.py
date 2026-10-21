"""One exact mixed-sign exterior/Clifford reconstruction, independent of source code."""

import json
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

N = 14
FULL = (1 << N) - 1
NEG = FULL ^ ((1 << 7) - 1)


def parity(a, b):
    return sum((b & ((1 << j) - 1)).bit_count() for j in range(N) if a >> j & 1) % 2


def wedge(a, b):
    return (0, 0) if a & b else ((-1) ** parity(a, b), a | b)


def cliff(a, b):
    return (-1) ** (parity(a, b) + (a & b & NEG).bit_count()), a ^ b


def plus(out, key, val):
    out[key] = out.get(key, F(0)) + val
    if not out[key]:
        del out[key]


def star(A):
    out = {}
    for (form, blade), c in A.items():
        complement = FULL ^ form
        sign = (-1) ** (parity(form, complement) + (form & NEG).bit_count())
        plus(out, (complement, blade), c * sign)
    return out


def product(A, B, mode):
    """Fixed exterior order, fiber commutator(mode=-1) or raw anticommutator(+1)."""
    out = {}
    for (a, x), c in A.items():
        for (b, y), d in B.items():
            ws, f = wedge(a, b)
            if not ws:
                continue
            s, z = cliff(x, y)
            t, w = cliff(y, x)
            assert z == w
            plus(out, (f, z), c * d * ws * (s + mode * t))
    return out


def scaled(A, s):
    return {key: c * s for key, c in A.items() if c * s}


def encode(A):
    return [
        {
            "exterior_indices": [i for i in range(N) if f >> i & 1],
            "clifford_indices": [i for i in range(N) if b >> i & 1],
            "coefficient": str(c),
        }
        for (f, b), c in sorted(A.items())
    ]


phi1 = {(1 << i, 1 << i): F(1) for i in range(N)}
phi2 = {((1 << i) | (1 << j), (1 << i) | (1 << j)): F(1) for i, j in combinations(range(N), 2)}
B = (1 << 0) | (1 << 7)
# R0707=-1, so rho07=s0*s7*R0707*E0E7=E0E7.
xi = {(B, B): F(1)}
first13 = product(phi1, star(xi), -1)
inner0_before_i = star(product(phi2, star(xi), 1))
# Two source Jordan products each contribute i; their composition has i*i=-1.
outer1 = scaled(product(phi1, inner0_before_i, 1), -1)
source13 = first13.copy()
for key, c in star(outer1).items():
    plus(source13, key, -c / 2)
identified = star(source13)
assert inner0_before_i == {(0, 0): F(2)}
expected = {(1 << i, 1 << i): F(2) for i in range(N) if i not in (0, 7)}
assert identified == expected
assert star(first13) == {(1, 1): F(-2), (1 << 7, 1 << 7): F(-2)}
# Old component Einstein contraction is0 on the section and-2Ei transversally.
component = scaled(expected, -1)
assert identified == scaled(component, -1)
# Reverse the sign of Phi1 in both occurrences, not just the Ricci term.
assert scaled(identified, -1) == component
out = {
    "signature": [7, 7],
    "orientation": list(range(N)),
    "basis_normalization": "Phi1=sum theta_i E_i; Phi2=sum_i<j theta_ij E_iE_j; xi=theta_07 E0E7",
    "input_R0707": "-1",
    "source_inner_scalar_before_i": encode(inner0_before_i),
    "source_degree13": encode(source13),
    "source_hodge_degree1": encode(identified),
    "old_component_degree1": encode(component),
    "conclusion": "Hodge(source9.3 comm/J/J instance)=-old_component; Phi1 sign reversal fixes equality",
    "scope": "One exact mixed-sign basis case. Source bracket/normalization assignment is declared, not author-uniquely recovered.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(
    "Exact mixed-sign case passes: identified source is -old component;12 transverse rows nonzero"
)
