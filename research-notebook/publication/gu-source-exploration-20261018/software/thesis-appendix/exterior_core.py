"""Exact independent reconstruction of Appendix A.1's elementary exterior operations.

Source: Weinstein dissertation (1992), printed p61 / PDF67. This is new Python,
not a transcription or execution of the printed Mathematica. Source convention:
Euclidean dimension eight, oriented basis 1..8, star = signed complement.
Signature support is our explicit extension; no claim that the thesis uses it.
No dependencies beyond Python standard library.
"""
from fractions import Fraction
from itertools import combinations


def sign(indices):
    if len(set(indices)) != len(indices):
        return 0
    return (-1) ** sum(a > b for i, a in enumerate(indices) for b in indices[i+1:])


def blade(*indices):
    s = sign(indices)
    return {tuple(sorted(indices)): Fraction(s)} if s else {}


def add(*forms):
    out = {}
    for form in forms:
        for key, value in form.items():
            out[key] = out.get(key, Fraction(0)) + value
    return {key: value for key, value in out.items() if value}


def scale(c, form):
    return {key: Fraction(c) * value for key, value in form.items() if c * value}


def wedge(left, right):
    out = {}
    for a, x in left.items():
        for b, y in right.items():
            key = tuple(sorted(a+b))
            out[key] = out.get(key, Fraction(0)) + x*y*sign(a+b)
    return {key: value for key, value in out.items() if value}


def hodge(form, signature=(1,)*8):
    if any(s not in (-1, 1) for s in signature):
        raise ValueError('Signature entries must be +1 or -1')
    out = {}
    for a, value in form.items():
        if a != tuple(sorted(set(a))) or not all(1 <= i <= len(signature) for i in a):
            raise ValueError('Forms require canonical in-range blade keys')
        b = tuple(i for i in range(1, len(signature)+1) if i not in a)
        metric = 1
        for i in a:
            metric *= signature[i-1]
        out[b] = value * sign(a+b) * metric
    return out


def source_interior(left, right):
    """Literal source composition star(left wedge star(right)), Euclidean n=8."""
    return hodge(wedge(left, hodge(right)))


def contract_vector(i, form, signature=(1,)*8):
    """Independent conventional contraction, used to check the source composition."""
    out = {}
    for a, value in form.items():
        if i in a:
            j = a.index(i)
            out[a[:j]+a[j+1:]] = value * (-1)**j * signature[i-1]
    return out


def cleave(form, polarity=1):
    if polarity not in (-1, 1) or any(len(a) != 4 for a in form):
        raise ValueError('Source cleave applies to degree four with polarity +/-1')
    return scale(Fraction(1,2), add(form, scale(polarity, hodge(form))))


def basis(n=8):
    return [blade(*a) for k in range(n+1) for a in combinations(range(1,n+1), k)]


def symbol(i, form):
    """Unprojected dee+delta on exterior factor; NOT thesis's final 448x448 map."""
    return add(wedge(blade(i), form), source_interior(blade(i), form))
