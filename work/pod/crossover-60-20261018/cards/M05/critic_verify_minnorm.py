"""Independent certificate consumer; does not import any producer module."""

import copy
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

N = 6


def require(condition, message):
    if not condition:
        raise ValueError(message)


def mat():
    return [[F(0) for _ in range(N)] for _ in range(N)]


def trans(a):
    return [list(c) for c in zip(*a, strict=True)]


def mult(a, b):
    return [
        [sum(x * y for x, y in zip(row, col, strict=True)) for col in zip(*b, strict=True)]
        for row in a
    ]


def plus(a, b, factor=F(1)):
    return [
        [x + factor * y for x, y in zip(ar, br, strict=True)] for ar, br in zip(a, b, strict=True)
    ]


def block(values):
    a = mat()
    for i, value in enumerate(values):
        a[2 * i][2 * i + 1], a[2 * i + 1][2 * i] = F(value), -F(value)
    return a


def identity():
    a = mat()
    for i in range(N):
        a[i][i] = F(1)
    return a


def vector(a):
    return [a[i][j] for i in range(N) for j in range(i + 1, N)]


def rank(a):
    a = copy.deepcopy(a)
    pivot = 0
    for col in range(len(a[0])):
        row = next((j for j in range(pivot, len(a)) if a[j][col]), None)
        if row is None:
            continue
        a[pivot], a[row] = a[row], a[pivot]
        divisor = a[pivot][col]
        a[pivot] = [v / divisor for v in a[pivot]]
        for j in range(len(a)):
            if j != pivot:
                factor = a[j][col]
                a[j] = [x - factor * y for x, y in zip(a[j], a[pivot], strict=True)]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def verify(record):
    t = F(record["t"])
    require(t in [F(1, n) for n in [2, 4, 8, 16, 32, 64]], "undeclared path parameter")
    k = block([1, 2, 3])
    q0 = mat()
    for i, j in enumerate([2, 3, 0, 1, 4, 5]):
        q0[i][j] = F(1)
    u = identity()
    co = (1 - t**2) / (1 + t**2)
    si = 2 * t / (1 + t**2)
    u[0][0] = u[4][4] = co
    u[0][4], u[4][0] = si, -si
    q = mult(mult(u, q0), trans(u))
    require(mult(q, q) == identity(), "involution model error")
    y = mult(mult(q, k), q)
    rhs = plus(mult(mult(k, k), k), plus(mult(mult(y, y), k), mult(k, mult(y, y))), F(-1, 2))
    bases = []
    for i in range(N):
        for j in range(i, N):
            h = mat()
            h[i][j] = h[j][i] = F(1)
            bases.append(h)
    gram = [sum(v * v for row in b for v in row) for b in bases]
    cols = [vector(plus(mult(mult(k, y), h), mult(h, mult(y, k)), -1)) for h in bases]
    expected_m = trans(cols)
    expected_b = vector(rhs)
    m = [[F(v) for v in row] for row in record["M"]]
    b = [F(v) for v in record["b"]]
    g = [F(v) for v in record["gram_diagonal"]]
    h = [F(v) for v in record["minimum_H_coefficients"]]
    z = [F(v) for v in record["dual_z"]]
    indices = record["independent_row_indices"]
    require(m == expected_m, "model-to-M binding")
    require(b == expected_b, "model-to-RHS binding")
    require(g == gram, "Frobenius Gram binding")
    require(len(h) == 21, "H dimension")
    require(len(indices) == len(set(indices)) == len(z), "dual row dimensions")
    require(all(isinstance(i, int) and 0 <= i < 15 for i in indices), "row index range")
    chosen = [m[i] for i in indices]
    require(rank(chosen) == len(chosen) == rank(m) == record["Phi_rank"], "rank/span")
    require(
        all(
            sum(x * v for x, v in zip(row, h, strict=True)) == r
            for row, r in zip(m, b, strict=True)
        ),
        "primal feasibility",
    )
    require(
        all(
            g[j] * h[j] == sum(row[j] * v for row, v in zip(chosen, z, strict=True))
            for j in range(21)
        ),
        "stationarity",
    )
    energy = sum(weight * v * v for weight, v in zip(g, h, strict=True))
    dual = sum(b[i] * v for i, v in zip(indices, z, strict=True))
    require(
        energy == dual == F(record["minimum_H_frobenius_squared"]) == F(record["dual_b_dot_z"]),
        "primal-dual value",
    )
    bound = F(1, 2) + energy / 14
    require(bound == F(record["s_squared_lower_bound"]), "symmetric-norm bound")
    require((bound >= 1) == record["excludes_s_below_one_for_every_inner_choice"], "decision")
    hm = mat()
    for value, bas in zip(h, bases, strict=True):
        hm = plus(hm, bas, value)
    a = mult(plus(hm, y, F(1, 2)), block([-1, F(-1, 2), F(-1, 3)]))
    require(plus(mult(a, k), mult(k, trans(a))) == y, "first original equation")
    require(plus(mult(trans(a), y), mult(y, a)) == k, "second original equation")
    return {
        "t": str(t),
        "minimum_H_squared": str(energy),
        "s_squared_lower": str(bound),
        "excludes_s_less_than_one": bound >= 1,
    }


def main():
    source = Path(__file__).with_name("inventor_minnorm.json")
    records = json.loads(source.read_text())
    require(len(records) == 6, "missing cases")
    require(
        {F(r["t"]) for r in records} == {F(1, n) for n in [2, 4, 8, 16, 32, 64]}, "case coverage"
    )
    verified = [verify(r) for r in records]
    rejections = []
    for record in records:
        for field in ["minimum_H_coefficients", "b", "dual_z"]:
            bad = copy.deepcopy(record)
            bad[field][0] = str(F(bad[field][0]) + 1)
            try:
                verify(bad)
            except ValueError as exc:
                rejections.append({"t": record["t"], "mutation": field, "rejected_by": str(exc)})
            else:
                raise ValueError("mutation accepted: " + field)
    result = {
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "producer_imported": False,
        "verified": verified,
        "negative_controls": rejections,
    }
    Path(__file__).with_name("critic_minnorm_results.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(
        json.dumps(
            {
                "cases_verified": len(verified),
                "mutations_rejected": len(rejections),
                "verified": verified,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
