"""Independent tuple-based external-form/Clifford audit; no producer imports."""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
N = 14
SIG = (1,) * 7 + (-1,) * 7
ALL = tuple(range(N))


def sign_order(word):
    return -1 if sum(a > b for i, a in enumerate(word) for b in word[i + 1 :]) % 2 else 1


def exterior(a, b):
    if set(a) & set(b):
        return None, 0
    return tuple(sorted(a + b)), sign_order(a + b)


def cliff(a, b):
    # Insert each right generator into a sorted word, crossing only larger indices.
    word = list(a)
    sgn = 1
    for x in b:
        sgn *= (-1) ** sum(y > x for y in word)
        if x in word:
            word.remove(x)
            sgn *= SIG[x]
        else:
            word.append(x)
            word.sort()
    return tuple(word), sgn


def add(out, k, v):
    out[k] = out.get(k, F(0)) + v
    if out[k] == 0:
        del out[k]


def combine(a, b, scale=F(1)):
    r = dict(a)
    for k, v in b.items():
        add(r, k, scale * v)
    return r


def wedge_bracket(a, b, mode):
    r = {}
    for (fa, ca), va in a.items():
        for (fb, cb), vb in b.items():
            form, sf = exterior(fa, fb)
            if not sf:
                continue
            ab, sab = cliff(ca, cb)
            ba, sba = cliff(cb, ca)
            add(r, (form, ab), sf * sab * va * vb)
            add(r, (form, ba), mode * sf * sba * va * vb)
    return r


def star(a):
    r = {}
    for (form, c), v in a.items():
        complement = tuple(i for i in ALL if i not in form)
        coefficient = sign_order(form + complement)
        for i in form:
            coefficient *= SIG[i]
        add(r, (complement, c), v * coefficient)
    return r


def tensor(seeds):
    out = {}
    for (a, b, c, d), v in seeds.items():
        for i, j, s in [(a, b, 1), (b, a, -1)]:
            for k, l, t in [(c, d, 1), (d, c, -1)]:
                out[i, j, k, l] = F(v * s * t)
                out[k, l, i, j] = F(v * s * t)
    return out


PHI1 = {((i,), (i,)): F(1) for i in ALL}
PHI2 = {(ij, ij): F(1) for ij in itertools.combinations(ALL, 2)}


def serialize(a):
    return [
        {"external": list(f), "clifford": list(c), "coefficient": str(v)}
        for (f, c), v in sorted(a.items())
    ]


def audit(name, R):
    rho = {
        ((i, j), (k, l)): SIG[k] * SIG[l] * v
        for (i, j, k, l), v in R.items()
        if i < j and k < l and v
    }
    first = wedge_bracket(PHI1, star(rho), -1)
    inner_raw = star(wedge_bracket(PHI2, star(rho), 1))
    outer_raw = star(wedge_bracket(PHI1, inner_raw, 1))
    # Two source Jordan products each carry i, hence subtraction becomes plus.
    literal = combine(first, outer_raw, F(1, 2))
    identified = star(literal)
    C = {}
    A = {}
    S = {}
    for i in ALL:
        for j in ALL:
            for k, l in itertools.combinations(ALL, 2):
                v = SIG[j] * SIG[k] * SIG[l] * R.get((j, i, k, l), 0)
                if not v:
                    continue
                ab, sab = cliff((j,), (k, l))
                ba, sba = cliff((k, l), (j,))
                add(C, ((i,), ab), v * sab)
                add(C, ((i,), ba), -v * sba)
                add(A, ((i,), ab), v * sab)
                add(A, ((i,), ba), v * sba)
    for i, j in itertools.combinations(ALL, 2):
        for k, l in itertools.combinations(ALL, 2):
            v = SIG[i] * SIG[j] * SIG[k] * SIG[l] * R.get((i, j, k, l), 0)
            if not v:
                continue
            ab, sab = cliff((i, j), (k, l))
            ba, sba = cliff((k, l), (i, j))
            add(S, ((), ab), v * sab)
            add(S, ((), ba), v * sba)
    E = combine(C, wedge_bracket(PHI1, S, 1), F(1, 2))
    assert identified == {k: -v for k, v in E.items()}
    ric = {(i, l): sum(SIG[j] * R.get((j, i, j, l), 0) for j in ALL) for i in ALL for l in ALL}
    scalar = sum(SIG[i] * ric[i, i] for i in ALL)
    bianchi = sum(
        R.get((i, j, k, l), 0) + R.get((i, k, l, j), 0) + R.get((i, l, j, k), 0) != 0
        for i, j, k, l in itertools.product(ALL, repeat=4)
    )
    target = {}
    for i in ALL:
        for l in ALL:
            value = 2 * SIG[l] * (ric[i, l] - F(1, 2) * scalar * (SIG[i] if i == l else 0))
            if value:
                add(target, ((i,), (l,)), value)
    if bianchi == 0:
        assert E == target and not A
    else:
        assert E != target and A
    # Removing i factors flips the entire scalar correction, not a harmless label.
    no_i = star(combine(first, outer_raw, F(-1, 2)))
    if scalar:
        assert no_i != identified
    assert all(len(form) == 13 for form, c in literal)
    return {
        "name": name,
        "bianchi_violations": bianchi,
        "scalar": str(scalar),
        "component_C": serialize(C),
        "raw_scalar_Jordan": serialize(S),
        "vector_anticommutator": serialize(A),
        "component_E": serialize(E),
        "source13_Hodge_identified": serialize(identified),
        "bridge": "literal9.3 with C/J/J, canonical sorted inclusions and standard split Hodge gives -E",
        "matches_Einstein_only_on_declared_Riemann_cases": bianchi == 0,
        "missing_i_mutation_detected": bool(scalar) and no_i != identified,
    }


def main():
    for k in [0, 1, 2, 13, 14]:
        for I in itertools.combinations(ALL, k):
            a = {(I, ()): F(1)}
            assert star(star(a)) == {(I, ()): F((-1) ** (k * (N - k) + 7))}
    cases = [
        audit("mixed07", tensor({(0, 7, 0, 7): -1})),
        audit("Bianchi_bad0123", tensor({(0, 1, 2, 3): 1})),
        audit("positive01", tensor({(0, 1, 0, 1): 1})),
    ]
    (P / "critic_operator.json").write_text(
        json.dumps(
            {
                "signature": SIG,
                "conventions": {
                    "external_basis": "ordered orthonormal covectors theta0..theta13",
                    "Hodge": "alpha wedge star alpha=<alpha,alpha> volume",
                    "Clifford": "ei²=signaturei",
                    "Phi1": "sum theta_i tensor ei",
                    "Phi2": "sum_i<j theta_ij tensor ei ej",
                    "curvature": "sum_i<j theta_ij tensor sum_k<l sksl Rijkl ekel",
                    "Jordan": "i(ab+ba), no half factor",
                    "scope": "One fixed interpretation of unlabelled source brackets, not uniquely author-selected",
                },
                "cases": cases,
            },
            indent=2,
        )
        + "\n"
    )
    print([(c["name"], c["scalar"], c["bianchi_violations"]) for c in cases])


if __name__ == "__main__":
    main()
