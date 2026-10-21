"""Independent determinant arithmetic plus a literal second source block.

Full-matrix input artifacts are shared with PM and independently reconstructed by critic.
No PM map, component, or determinant routine is imported.
"""

import json
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import domain_double as d

P = Path(__file__).resolve().parent
B = d.bases()


def det(matrix):
    """Laplace expansion with memoized column subsets; no elimination/pivot signs."""
    n = len(matrix)

    @lru_cache(None)
    def expand(columns):
        if not columns:
            return F(1)
        row = n - len(columns)
        return sum(
            (
                (-1) ** k * matrix[row][col] * expand(columns[:k] + columns[k + 1 :])
                for k, col in enumerate(columns)
                if matrix[row][col]
            ),
            F(0),
        )

    return expand(tuple(range(n)))


def source_block(a, b):
    """The 5a+6b block: w123 plus first Y2/Y4+ chains."""
    z = d.tensor(d.blade(), d.blade(1, 2, 3))
    l3 = d.add(d.scale(a, d.map_right(d.raise_(z), d.cleavep)), d.scale(b, d.shift(z)))
    inputs = [l3] + B["Y2"][:2] + B["Y4p"][:4]
    rows = []
    for x in inputs:
        bp = d.map_left(x, lambda u: d.add(d.wedge(d.blade(1), u), d.interior(d.blade(1), u)))
        y3, l2, y1 = {}, {}, {}
        for (u, v), coef in bp.items():
            term = {(u, v): coef}
            degree = len(u), len(v)
            if degree == (2, 4):
                y3 = d.add(y3, d.projY(d.lower(term)))
                l2 = d.add(l2, d.i(term))
            if degree == (2, 2):
                y3 = d.add(y3, d.projY(d.flip(d.shift(term))))
                l2 = d.add(l2, d.e(d.lower(term)))
                y1 = d.add(y1, d.projY(d.lower(term)))
            if degree == (0, 2):
                l2 = d.add(l2, {v: -coef})
        rows.append(
            [2 * d.sp(y3, t) for t in B["Y3"][245:250]]
            + [2 * d.sp(l2, B["L2"][7]), 2 * d.sp(y1, B["Y1"][7])]
        )
    return rows


literal = [det(source_block(a, b)) for a, b in [(1, 0), (0, 1), (2, -1), (6, -5)]]
assert literal == [3200, 3840, 2560, 0]


def read(index):
    raw = json.loads((P / f"pm_matrix_A_{index}.json").read_text())
    return [{j: F(v) for j, v in row} for row in raw["rows"]]


A, Bmat = read(4), read(5)
# Build support union, independent of PM component lists.
adj = [set() for _ in range(896)]
for r in range(448):
    for c in A[r].keys() | Bmat[r].keys():
        adj[r].add(448 + c)
        adj[448 + c].add(r)
seen = set()
blocks = []
for start in range(896):
    if start in seen:
        continue
    todo, component = [start], set()
    while todo:
        x = todo.pop()
        if x in component:
            continue
        component.add(x)
        todo.extend(adj[x] - component)
    seen |= component
    blocks.append(
        (sorted(x for x in component if x < 448), sorted(x - 448 for x in component if x >= 448))
    )


def sign(sequence):
    return (-1) ** sum(
        sequence[i] > sequence[j] for i in range(len(sequence)) for j in range(i + 1, len(sequence))
    )


constant = F(sign([r for rs, _ in blocks for r in rs]) * sign([c for _, cs in blocks for c in cs]))
counts = Counter()
records = []
for rs, cs in blocks:
    assert len(rs) == len(cs) == 7
    da = det([[A[r].get(c, 0) for c in cs] for r in rs])
    db = det([[Bmat[r].get(c, 0) for c in cs] for r in rs])
    changing = [r for r in rs if A[r] != Bmat[r]]
    if not changing:
        assert da == db
        kind = "constant"
        constant *= da
    else:
        assert len(changing) == 1 and 8 <= changing[0] < 64
        ratio = db / da
        assert ratio in (F(6, 5), F(-3, 5))
        kind = "5a+6b" if ratio == F(6, 5) else "5a-3b"
        constant *= da / 5
    counts[kind] += 1
    records.append({"rows": rs, "columns": cs, "da": str(da), "db": str(db), "kind": kind})
assert counts == {"constant": 8, "5a+6b": 21, "5a-3b": 35}
assert constant == 2**491 * 3**43 * 5**21 * 7**8
result = {
    "method": "Independent support union and Laplace subset determinant, shared input matrices.",
    "literal_second_source_block_a_b_points": [[1, 0], [0, 1], [2, -1], [6, -5]],
    "literal_second_source_block_determinants": list(map(str, literal)),
    "block_counts": dict(counts),
    "constant": str(constant),
    "blocks": records,
    "formula": "2^491*3^43*5^21*7^8*(5a+6b)^21*(5a-3b)^35",
    "binding": "Source injection is linear in a,b only on the 56 L3 rows. Other rows fixed. Each block has at most one changing row. Domain first and second literal blocks independently validate both linear factors. Full entry reconstruction independence is supplied by critic, not this shared-data audit.",
    "limits": "Exact Fraction executable identity; not a Lean certificate or a resolution of printed A3/A4 signs.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(result["formula"])
print(result["block_counts"])
