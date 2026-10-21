"""Independent sparse-graph exact determinant and rational null certificate check."""

import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = Path(
    "/Users/mike/Dev/ctrl-research-notebook/research-notebook/publication/gu-source-exploration-20261018/software/thesis-appendix/determinant-fixtures.json"
)
fixtures = json.loads(FIX.read_text())["fixtures"]


def parity(order):
    return (-1) ** sum(x > y for i, x in enumerate(order) for y in order[i + 1 :])


def eliminate(A, n):
    rows = [{int(j): F(x) for j, x in r.items() if x} for r in A]
    piv = []
    det = F(1)
    k = 0
    for col in range(n):
        source = next((i for i in range(k, len(rows)) if rows[i].get(col, 0)), None)
        if source is None:
            continue
        if source != k:
            rows[k], rows[source] = rows[source], rows[k]
            det = -det
        z = rows[k][col]
        det *= z
        rows[k] = {j: x / z for j, x in rows[k].items()}
        for i in range(len(rows)):
            if i == k:
                continue
            fac = rows[i].get(col, 0)
            if fac:
                for j, v in rows[k].items():
                    a = rows[i].get(j, F(0)) - fac * v
                    if a:
                        rows[i][j] = a
                    else:
                        rows[i].pop(j, None)
        piv.append(col)
        k += 1
        if k == len(rows):
            break
    return rows, piv, det if len(piv) == n == len(rows) else F(0)


def components(A, n):
    adj = {i: set() for i in range(2 * n)}
    for i, row in enumerate(A):
        for j in row:
            adj[i].add(n + j)
            adj[n + j].add(i)
    unseen = set(adj)
    out = []
    while unseen:
        stack = [min(unseen)]
        group = set()
        while stack:
            x = stack.pop()
            if x in group:
                continue
            group.add(x)
            stack.extend(adj[x] - group)
        unseen -= group
        out.append((sorted(x for x in group if x < n), sorted(x - n for x in group if x >= n)))
    return out


results = []
for f in fixtures:
    data = json.loads((HERE / ("pm_matrix_" + f["label"].replace(".", "_") + ".json")).read_text())
    assert data["coefficients"] == f["coefficients"] and data["dimension"] == 448
    A = [{j: F(x) for j, x in row} for row in data["rows"]]
    assert len(A) == 448
    groups = components(A, 448)
    rd = []
    cd = []
    D = F(1)
    blocks = []
    for rr, cc in groups:
        if len(rr) != len(cc):
            D = F(0)
            break
        local = [{j: A[i].get(c, F(0)) for j, c in enumerate(cc) if A[i].get(c, 0)} for i in rr]
        _, p, d = eliminate(local, len(cc))
        D *= d
        rd += rr
        cd += cc
        blocks.append({"dimension": len(rr), "rank": len(p), "det": str(d)})
    if D:
        D *= parity(rd) * parity(cd)
    expected = f["determinant_sign"]
    for p, e in f["prime_factorization_abs"].items():
        expected *= int(p) ** e
    out = {
        "label": f["label"],
        "components": len(groups),
        "largest_component": max(max(len(a), len(b)) for a, b in groups),
        "exact_determinant": str(D),
        "source_determinant": str(expected),
        "ratio_to_source": str(D / expected) if expected else None,
        "matches_exactly": D == expected,
        "blocks": blocks,
    }
    if not D:
        reduced, pivots, _ = eliminate(A, 448)
        free = next(j for j in range(448) if j not in pivots)
        v = {free: F(1)}
        for row, pivot in zip(reduced, pivots, strict=False):
            if row.get(free, 0):
                v[pivot] = -row[free]
        assert v and all(sum(a * v.get(j, 0) for j, a in row.items()) == 0 for row in A)
        out["rational_rank"] = len(pivots)
        out["right_null_vector"] = {str(j): str(x) for j, x in v.items()}
        out["null_scope"] = (
            "Exact right-null vector of stored row-input matrix: a target-coordinate annihilator, not yet a classified geometric source kernel."
        )
        # A changed coefficient in one row must invalidate this particular witness.
        row = next(i for i, r in enumerate(A) if r)
        col = free
        mutated = [dict(r) for r in A]
        mutated[row][col] = mutated[row].get(col, 0) + 1
        assert any(sum(a * v.get(j, 0) for j, a in r.items()) != 0 for r in mutated)
        out["null_witness_matrix_entry_mutation_rejected"] = True
    results.append(out)
    (HERE / "critic_symbol.json").write_text(
        json.dumps(
            {
                "method": "Independent connected bipartite components, rational Gauss-Jordan elimination, exact row/column permutation signs. No producer determinant routine imported.",
                "results": results,
            },
            indent=2,
        )
        + "\n"
    )
    print(
        f["label"],
        out["components"],
        out["largest_component"],
        out["ratio_to_source"],
        out.get("rational_rank"),
        flush=True,
    )
