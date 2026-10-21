"""Independent exact consumer for the named SO2 cycle certificate and mutations."""

import copy
import json
from fractions import Fraction as F
from pathlib import Path


def T(a):
    return [list(row) for row in zip(*a, strict=True)]


def product(a, b):
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def rational(a):
    return [[F(v) for v in row] for row in a]


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def proper(a):
    return product(T(a), a) == eye(2) and a[0][0] * a[1][1] - a[0][1] * a[1][0] == 1


def normalized_edges(edges):
    result = []
    for edge in edges:
        i, j, w, m = edge["i"], edge["j"], F(edge["weight"]), rational(edge["measurement"])
        assert 0 <= i < 3 and 0 <= j < 3 and i != j and w > 0 and proper(m)
        if i > j:
            i, j, m = j, i, T(m)
        result.append((i, j, w, m))
    return sorted(result, key=lambda x: (x[0], x[1]))


def rank(a):
    a = copy.deepcopy(a)
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        v = a[row][col]
        a[row] = [x / v for x in a[row]]
        for i in range(len(a)):
            if i != row:
                v = a[i][col]
                a[i] = [x - v * y for x, y in zip(a[i], a[row], strict=True)]
        row += 1
    return row


def verify(cert, trusted_edges):
    assert cert["group"] == "SO(2)" and cert["anchor"] == "R0=I"
    edges = normalized_edges(cert["edges"])
    assert edges == normalized_edges(trusted_edges)
    reached = {0}
    while True:
        nxt = (
            reached
            | {j for i, j, w, m in edges if i in reached}
            | {i for i, j, w, m in edges if j in reached}
        )
        if nxt == reached:
            break
        reached = nxt
    assert reached == {0, 1, 2}, "one anchor does not fix disconnected components"
    R = [rational(v) for v in cert["rotations"]]
    assert len(R) == 3 and all(proper(v) for v in R) and R[0] == eye(2)
    Q = [[F(0) for _ in range(6)] for _ in range(6)]
    cost = F(0)
    for i, j, w, m in edges:
        pred = product(R[i], m)
        cost += w * sum((R[j][a][b] - pred[a][b]) ** 2 for a in range(2) for b in range(2))
        for a in range(2):
            Q[2 * i + a][2 * i + a] += w
            Q[2 * j + a][2 * j + a] += w
            for b in range(2):
                Q[2 * i + a][2 * j + b] -= w * m[a][b]
                Q[2 * j + b][2 * i + a] -= w * m[a][b]
    assert rational(cert["laplacian"]) == Q
    lam = list(map(F, cert["dual_node_scalars"]))
    assert len(lam) == 3
    S = [[Q[i][j] - (lam[i // 2] if i == j else 0) for j in range(6)] for i in range(6)]
    assert S == rational(cert["slack"]) and S == T(S)
    L = rational(cert["ldl_L"])
    D = list(map(F, cert["ldl_D"]))
    assert len(D) == 6 and all(x >= 0 for x in D)
    assert all(L[i][j] == (1 if i == j else 0) for i in range(6) for j in range(i, 6))
    assert [
        [sum(L[i][k] * D[k] * L[j][k] for k in range(6)) for j in range(6)] for i in range(6)
    ] == S
    X = [[v for rot in R for v in rot[a]] for a in range(2)]
    assert product(X, S) == [[0] * 6 for _ in range(2)]
    assert cost == F(cert["objective"]) == 2 * sum(lam)
    assert rank(S) == cert["rank"] == 4 and rank(X) == 2
    # Uniqueness: ker(S) has exactly these two independent rows; R0 anchor fixes their linear combination.
    return {
        "objective": str(cost),
        "slack_rank": rank(S),
        "anchored_unique": "conditional exact weak-duality/kernel argument, SO2 model",
        "graph_edges": len(edges),
    }


def main():
    p = Path(__file__).resolve().parent
    cert = json.loads((p / "pm_rational_cycle.json").read_text())
    trusted = [
        {"i": 0, "j": 1, "weight": "1", "measurement": [["1", "0"], ["0", "1"]]},
        {"i": 1, "j": 2, "weight": "1", "measurement": [["1", "0"], ["0", "1"]]},
        {
            "i": 0,
            "j": 2,
            "weight": "1",
            "measurement": [["-44/125", "-117/125"], ["117/125", "-44/125"]],
        },
    ]
    positive = verify(cert, trusted)
    tests = []

    def reject(name, mutator, other_trusted=None):
        c = copy.deepcopy(cert)
        mutator(c)
        try:
            verify(c, trusted if other_trusted is None else other_trusted)
        except (AssertionError, ValueError, IndexError):
            tests.append({"name": name, "rejected": True})
        else:
            raise AssertionError(name + " was accepted")

    reject("single reflection", lambda c: c["rotations"].__setitem__(1, [["1", "0"], ["0", "-1"]]))
    reject("missing anchor", lambda c: c.__setitem__("anchor", "none"))
    reject("wrong group O2", lambda c: c.__setitem__("group", "O(2)"))
    reject("changed edge weight", lambda c: c["edges"][0].__setitem__("weight", "2"))
    reject("negative weight", lambda c: c["edges"][0].__setitem__("weight", "-1"))
    reject("reversed edge without inverse", lambda c: c["edges"][2].update({"i": 2, "j": 0}))
    reject(
        "changed measurement sign",
        lambda c: c["edges"][2]["measurement"][0].__setitem__(1, "117/125"),
    )
    reject("changed claimed objective scale", lambda c: c.__setitem__("objective", "6/5"))
    reject("wrong dual coefficient", lambda c: c["dual_node_scalars"].__setitem__(0, "1/5"))
    reject("negative tiny LDL pivot", lambda c: c["ldl_D"].__setitem__(5, "-1/1000000000000"))
    reject("mutated factor", lambda c: c["ldl_L"][4].__setitem__(1, "117/200"))
    reject("mutated slack", lambda c: c["slack"][0].__setitem__(0, "1599999999999/1000000000000"))
    reject("mutated laplacian", lambda c: c["laplacian"][0].__setitem__(5, "-117/125"))
    reject("incorrect rank", lambda c: c.__setitem__("rank", 2))
    reject(
        "different feasible suboptimal primal",
        lambda c: c.__setitem__("rotations", [[["1", "0"], ["0", "1"]]] * 3),
    )
    reject("nonrational nan", lambda c: c["ldl_D"].__setitem__(0, "nan"))
    reject("omitted cycle edge", lambda c: c["edges"].pop())
    reject(
        "different proper measurement",
        lambda c: c["edges"][2].__setitem__("measurement", [["1", "0"], ["0", "1"]]),
    )

    def gauge_mutation(c):
        G = [[F(0), F(-1)], [F(1), F(0)]]
        c["rotations"] = [
            [[str(v) for v in row] for row in product(G, rational(R))] for R in c["rotations"]
        ]

    reject("unfixed common gauge", gauge_mutation)
    disconnected = [trusted[0]]
    reject(
        "disconnected graph one anchor",
        lambda c: c.__setitem__("edges", disconnected),
        disconnected,
    )
    reverse = copy.deepcopy(cert)
    reverse["edges"][2].update(
        {"i": 2, "j": 0, "measurement": T(reverse["edges"][2]["measurement"])}
    )
    assert verify(reverse, trusted) == positive
    # Approximate eigentest is unsound: exact negative direction despite tolerance.
    eps = F(1, 10**12)
    bad = [[F(1), 0], [0, -eps]]
    assert bad[1][1] < 0 and float(bad[1][1]) >= -1e-9
    (p / "critic_certificate.json").write_text(
        json.dumps(
            {
                "positive": positive,
                "mutations": tests,
                "inverse_edge_reorientation_accepted": True,
                "approximate_PSD_negative": {
                    "matrix": [["1", "0"], ["0", str(-eps)]],
                    "direction": [0, 1],
                    "quadratic_value": str(-eps),
                    "tolerance_minus1e_9_would_accept": True,
                },
                "producer_imports": False,
            },
            indent=2,
        )
        + "\n"
    )
    print(positive, "rejected", len(tests))


if __name__ == "__main__":
    main()
