"""Exact Appendix A double forms. Source projection semantics; provisional Plus term order."""

import importlib.util
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from pathlib import Path

CORE = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/exterior_core.py"
)
spec = importlib.util.spec_from_file_location("m07_exterior", CORE)
ext = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ext)
add = ext.add
scale = ext.scale
blade = ext.blade
wedge = ext.wedge
star = ext.hodge
interior = ext.source_interior


def cleavep(a):
    return ext.cleave(a, 1)


def tensor(a, b):
    return {(x, y): u * v for x, u in a.items() for y, v in b.items() if u * v}


def linear(d, fn):
    return add(*(scale(c, dict(fn(a, b))) for (a, b), c in d.items()))


def flip(d):
    return {(b, a): c for (a, b), c in d.items()}


def map_left(d, fn):
    return add(*(scale(c, tensor(fn({a: F(1)}), {b: F(1)})) for (a, b), c in d.items()))


def map_right(d, fn):
    return add(*(scale(c, tensor({a: F(1)}, fn({b: F(1)}))) for (a, b), c in d.items()))


@lru_cache(None)
def raise_blade(a, b):
    return tuple(
        add(
            *(tensor(wedge({a: F(1)}, blade(j)), wedge(blade(j), {b: F(1)})) for j in range(1, 9))
        ).items()
    )


def raise_(d):
    return linear(d, raise_blade)


def shift(d):
    return map_right(raise_(map_right(d, star)), star)


def lower(d):
    return map_right(map_left(raise_(map_right(map_left(d, star), star)), star), star)


def e(d):
    return add(*(scale(c, wedge({a: F(1)}, {b: F(1)})) for (a, b), c in d.items()))


def i(d):
    return add(*(scale(c, interior({a: F(1)}, {b: F(1)})) for (a, b), c in d.items()))


@lru_cache(None)
def projY_blade(a, b):
    assert len(a) == 1
    n = len(b)
    z = tensor({a: F(1)}, {b: F(1)})
    return tuple(
        add(
            z,
            scale(-F(1, 9 - n), raise_(tensor(blade(), i(z)))),
            scale(-F(1, n + 1), shift(tensor(blade(), e(z)))),
        ).items()
    )


def projY(d):
    return linear(d, projY_blade)


def differences(terms):
    # Mathematica Plus canonical order not yet independently established.
    # All signed summands are retained; only their order is provisionally lexicographic.
    z = [{k: v} for k, v in sorted(terms.items())]
    return [add(z[j], scale(-1, z[j + 1])) for j in range(len(z) - 1)]


def bases():
    L1 = [blade(j) for j in range(1, 9)]
    L2 = [blade(*s) for s in combinations(range(1, 9), 2)]
    L3 = [blade(*s) for s in combinations(range(1, 9), 3)]
    L4p = [cleavep(blade(*s)) for s in combinations(range(1, 8), 4)]
    Y1 = [
        add(tensor(blade(j), blade(k)), tensor(blade(k), blade(j)))
        for j in range(1, 8)
        for k in range(j + 1, 9)
    ]
    Y1 += [
        add(tensor(blade(j), blade(j)), scale(-1, tensor(blade(j + 1), blade(j + 1))))
        for j in range(1, 8)
    ]
    Y2 = []
    for a in L3:
        Y2.extend(differences(shift(tensor(blade(), a))))
    for a in L1:
        Y2.extend(differences(raise_(tensor(blade(), a))))
    Y3 = []
    for s in combinations(range(1, 9), 4):
        Y3.extend(differences(shift(tensor(blade(), blade(*s)))))
    for a in L2:
        Y3.extend(differences(raise_(tensor(blade(), a))))
    Y4p = []
    for a in L3:
        z = raise_(tensor(blade(), a))
        # Source takes a List of five raised summands, then stars each matching term.
        terms = [{k: v} for k, v in sorted(z.items())]
        paired = [add(t, map_right(t, star)) for t in terms]
        Y4p.extend(add(paired[j], scale(-1, paired[j + 1])) for j in range(4))
    return {"L1": L1, "L2": L2, "L3": L3, "L4p": L4p, "Y1": Y1, "Y2": Y2, "Y3": Y3, "Y4p": Y4p}


def sp(a, b):
    return sum((v * b.get(k, F(0)) for k, v in a.items()), F(0))
