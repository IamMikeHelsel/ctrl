"""Exact full linear-basis bridge under DECLARED Phi1/Phi2 and C/J/J conventions.
External wedge degree and internal Clifford blade are independent tensor legs.
Two Jordan i factors are combined explicitly as i*i=-1. No source uniqueness claim.
"""

import json
from itertools import combinations
from pathlib import Path

N = 14
FULL = (1 << N) - 1
NEG = FULL ^ ((1 << 7) - 1)
PAIRS = [(i, j) for i, j in combinations(range(N), 2)]


def parity(a, b):
    return -1 if sum((b & ((1 << j) - 1)).bit_count() for j in range(N) if a >> j & 1) % 2 else 1


def metric(a):
    return -1 if (a & NEG).bit_count() % 2 else 1


def cliff(a, b):
    return parity(a, b) * metric(a & b), a ^ b


def bracket(a, b, mode):
    s, m = cliff(a, b)
    t, n = cliff(b, a)
    assert m == n
    return s + mode * t, m


def add(out, key, value):
    out[key] = out.get(key, 0) + value
    if not out[key]:
        del out[key]


def star(form, orientation=1):
    out = {}
    for (a, b), c in form.items():
        comp = FULL ^ a
        add(out, (comp, b), c * metric(a) * parity(a, comp) * orientation)
    return out


def wedge_bracket(left, right, mode):
    out = {}
    for (a, b), c in left.items():
        for (d, e), f in right.items():
            if a & d:
                continue
            sign, mask = bracket(b, e, mode)
            add(out, (a | d, mask), c * f * parity(a, d) * sign)
    return out


PHI1 = {(1 << i, 1 << i): 1 for i in range(N)}
PHI2 = {((1 << i) | (1 << j), (1 << i) | (1 << j)): 1 for i, j in PAIRS}


def source_twice(xi, orientation=1):
    sx = star(xi, orientation)
    first = wedge_bracket(PHI1, sx, -1)
    inner = star(wedge_bracket(PHI2, sx, +1), orientation)
    outer = star(wedge_bracket(PHI1, inner, +1), orientation)
    # Displayed minus1/2 times two Jordan products = plus1/2 times two raw anti products.
    out = {k: 2 * v for k, v in first.items()}
    for key, c in outer.items():
        add(out, key, c)
    return out


def component_twice(i, j, b):
    out = {}
    for row, v, sg in [(j, i, metric(1 << i)), (i, j, -metric(1 << j))]:
        c, m = bracket(1 << v, b, -1)
        add(out, (1 << row, m), 2 * sg * c)
    c, m = bracket((1 << i) | (1 << j), b, +1)
    c *= metric((1 << i) | (1 << j))
    for r in range(N):
        d, n = bracket(1 << r, m, +1)
        add(out, (1 << r, n), c * d)
    return out


def main():
    count = 0
    wrong_sign_detected = 0
    for i, j in PAIRS:
        for k, l in PAIRS:
            b = (1 << k) | (1 << l)
            xi = {((1 << i) | (1 << j), b): 1}
            s = source_twice(xi)
            identified = star(s)
            comp = component_twice(i, j, b)
            assert identified == {x: -v for x, v in comp.items()}
            assert all(a.bit_count() == 13 for a, _ in s)
            assert all(a.bit_count() == 1 for a, _ in identified)
            # Reverse orientation consistently on every star: degree13 flips; degree1 bridge does not.
            reversed_source = source_twice(xi, -1)
            assert reversed_source == {x: -v for x, v in s.items()}
            assert star(reversed_source, -1) == identified
            wrong_sign_detected += identified != comp
            count += 1
    # Standard Hodge square independently checked on every exterior blade.
    for a in range(1 << N):
        sign = (-1) ** (a.bit_count() * (N - a.bit_count()) + 7)
        assert star(star({(a, 0): 1})) == {(a, 0): sign}
    out = {
        "basis_cases": count,
        "exterior_blades_hodge_square": 1 << N,
        "wrong_global_plus_sign_detected_cases": wrong_sign_detected,
        "identity": "star(displayed9.3_nesting_with_declared_CJJ(xi)) = -E_component(xi)",
        "domain": "all exterior2-forms with Clifford-bivector coefficients; Riemann symmetries NOT required for this translation",
        "conventions": "orientationtheta0...theta13; metricdiag(+7,-7); sorted wedge coefficients; Phi1=sumtheta_i tensor e_i; Phi2=sum_i<jtheta_ij tensor e_i e_j; commutator then i-anticommutator twice",
        "orientation": "consistent orientation reversal negates degree13 expression but preserves its Hodge-identified degree1 value",
        "limitations": "Python exact linear-basis evidence; kernel linearity/basis completeness assembly and author-selected normalization remain open; Einstein interpretation requires Riemann assumptions",
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out))


if __name__ == "__main__":
    main()
