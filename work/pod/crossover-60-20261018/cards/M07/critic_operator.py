"""Independent bit-mask exterior operator; declared shared provisional basis list."""

import importlib.util
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("producer_basis_only", HERE / "domain_double.py")
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)


def mask(t):
    return sum(1 << (j - 1) for j in t)


def convert(v):
    return {
        (tuple(mask(a) for a in k) if k and isinstance(k[0], tuple) else mask(k)): Q(c)
        for k, c in v.items()
    }


B = {k: [convert(v) for v in vs] for k, vs in shared.bases().items()}


def plus(*vs):
    out = {}
    for v in vs:
        for k, c in v.items():
            out[k] = out.get(k, Q(0)) + c
    return {k: c for k, c in out.items() if c}


def scale(c, v):
    return {k: c * x for k, x in v.items() if c * x}


def ws(a, b):
    if a & b:
        return 0
    return (-1) ** sum((b & ((1 << i) - 1)).bit_count() for i in range(8) if a & (1 << i))


def wedge(a, b):
    return plus(
        *({i | j: c * d * ws(i, j)} for i, c in a.items() for j, d in b.items() if ws(i, j))
    )


def star(v):
    return {255 ^ k: c * ws(k, 255 ^ k) for k, c in v.items()}


def interior(a, b):
    return star(wedge(a, star(b)))


def tensor(a, b):
    return {(i, j): c * d for i, c in a.items() for j, d in b.items()}


def left(v, fn):
    return plus(*(scale(c, tensor(fn({i: Q(1)}), {j: Q(1)})) for (i, j), c in v.items()))


def right(v, fn):
    return plus(*(scale(c, tensor({i: Q(1)}, fn({j: Q(1)}))) for (i, j), c in v.items()))


def flip(v):
    return {(j, i): c for (i, j), c in v.items()}


def raise_(v):
    return plus(
        *(
            scale(c, tensor(wedge({i: Q(1)}, {1 << k: Q(1)}), wedge({1 << k: Q(1)}, {j: Q(1)})))
            for (i, j), c in v.items()
            for k in range(8)
        )
    )


def shift(v):
    return right(raise_(right(v, star)), star)


def lower(v):
    return right(left(raise_(right(left(v, star), star)), star), star)


def ex(v):
    return plus(*(scale(c, wedge({i: Q(1)}, {j: Q(1)})) for (i, j), c in v.items()))


def con(v):
    return plus(*(scale(c, interior({i: Q(1)}, {j: Q(1)})) for (i, j), c in v.items()))


def selfdual(v):
    return scale(Q(1, 2), plus(v, star(v)))


def young(v):
    out = {}
    for (i, j), c in v.items():
        assert i.bit_count() == 1
        z = {(i, j): Q(1)}
        n = j.bit_count()
        value = plus(
            z,
            scale(-Q(1, 9 - n), raise_(tensor({0: Q(1)}, con(z)))),
            scale(-Q(1, n + 1), shift(tensor({0: Q(1)}, ex(z)))),
        )
        out = plus(out, scale(c, value))
    return out


def image(group, x, c, covector=None):
    if covector is None:
        covector = {1: Q(1)}
    if group == "L1":
        x = raise_(tensor({0: Q(1)}, x))
    if group == "L3":
        y = tensor({0: Q(1)}, x)
        x = plus(scale(c[0], right(raise_(y), selfdual)), scale(c[1], shift(y)))
    y = left(x, lambda a: plus(wedge(covector, a), interior(covector, a)))
    ans = [{} for _ in range(4)]
    for (i, j), co in y.items():
        z = {(i, j): Q(1)}
        degree = (i.bit_count(), j.bit_count())
        if degree == (2, 4):
            parts = [
                scale(c[2], con(flip(shift(flip(z))))),
                scale(c[5], young(lower(z))),
                scale(c[7], con(z)),
                {},
            ]
        elif degree == (2, 2):
            parts = [
                scale(c[3], selfdual(ex(z))),
                scale(c[6], young(flip(shift(z)))),
                scale(c[8], ex(lower(z))),
                young(lower(z)),
            ]
        elif degree == (0, 4):
            parts = [scale(c[4], {j: Q(1)}), {}, {}, {}]
        elif degree == (0, 2):
            parts = [{}, {}, scale(c[9], {j: Q(1)}), {}]
        else:
            raise ValueError(degree)
        ans = [plus(a, scale(co, b)) for a, b in zip(ans, parts, strict=True)]
    return ans


# Primitive sign negatives distinguish reversal of contraction order.
assert interior({3: Q(1)}, {15: Q(1)}) == {12: Q(1)}
assert interior({1: Q(1)}, interior({2: Q(1)}, {15: Q(1)})) == {12: Q(-1)}
results = []
for num in range(1, 7):
    saved = json.loads((HERE / f"pm_matrix_A_{num}.json").read_text())
    c = saved["coefficients"]
    n = 0
    for group in ("L1", "L3", "Y2", "Y4p"):
        for x in B[group]:
            outputs = image(group, x, c)
            row = [
                2 * sum(val * t.get(k, Q(0)) for k, val in out.items())
                for out, name in zip(outputs, ("L4p", "Y3", "L2", "Y1"), strict=True)
                for t in B[name]
            ]
            sparse = {j: v for j, v in enumerate(row) if v}
            expected = {j: Q(v) for j, v in saved["rows"][n]}
            assert sparse == expected, (num, n)
            n += 1
    assert n == 448
    results.append({"fixture": num, "all_entries_match": True, "rows": n})
    print(num, "all448 rows match", flush=True)
(HERE / "critic_operator.json").write_text(
    json.dumps(
        {
            "results": results,
            "primitive_sign_negative_passed": True,
            "independence": "All exterior signs and double-form/projection operations freshly implemented with bit masks. Shares only provisional ordered basis vectors produced by domain_double.bases; no producer operator or determinant routine used. Projection formulas visually checked against source PDF69–70.",
            "remaining": "Mathematica2 Plus term ordering and source sign discrepancy remain unresolved; this is not a second completely independent source-basis transcription.",
        },
        indent=2,
    )
    + "\n"
)
