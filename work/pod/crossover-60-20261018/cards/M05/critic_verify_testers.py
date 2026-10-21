"""Consume fixed-symmetric-test lower-bound certificates without producer imports."""

import copy
import hashlib
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

BASE = Path(__file__).parent
v = runpy.run_path(str(BASE / "critic_verify_minnorm.py"), run_name="critic_library")
require, mult, plus, trans = v["require"], v["mult"], v["plus"], v["trans"]
mat, rank, block = v["mat"], v["rank"], v["block"]


def parse(a):
    return [[F(x) for x in row] for row in a]


def inner(a, b):
    return sum(x * y for ar, br in zip(a, b, strict=True) for x, y in zip(ar, br, strict=True))


def energy(a):
    return inner(a, a)


def lyap(a, s):
    return plus(mult(a, s), mult(s, trans(a)))


def verify(data, old, selected):
    v["verify"](old)
    require(old["t"] == "1/2", "parameter")
    k = block([1, 2, 3])
    ki = block([-1, F(-1, 2), F(-1, 3)])
    q0 = mat()
    for i, j in enumerate([2, 3, 0, 1, 4, 5]):
        q0[i][j] = F(1)
    u = v["identity"]()
    u[0][0] = u[4][4] = F(3, 5)
    u[0][4], u[4][0] = F(4, 5), F(-4, 5)
    q = mult(mult(u, q0), trans(u))
    y = mult(mult(q, k), q)
    require(parse(data["K"]) == k and parse(data["Y"]) == y, "pair binding")
    m = parse(old["M"])
    bases = []
    for i in range(6):
        for j in range(i, 6):
            h = mat()
            h[i][j] = h[j][i] = F(1)
            bases.append(h)

    def unvec(coeffs):
        h = mat()
        require(len(coeffs) == 21, "basis dimension")
        for c, b in zip(coeffs, bases, strict=True):
            h = plus(h, b, c)
        return h

    kernel = parse(data["kernel_H_coefficients"])
    require(len(kernel) == rank(kernel) == 21 - rank(m) == 9, "full kernel dimension")
    require(
        all(sum(x * h for x, h in zip(row, col, strict=True)) == 0 for row in m for col in kernel),
        "kernel annihilation",
    )
    h0 = unvec(list(map(F, old["minimum_H_coefficients"])))
    a0 = mult(plus(h0, y, F(1, 2)), ki)
    require(parse(data["particular_A_minH"]) == a0, "particular A")
    directions = [mult(unvec(coeffs), ki) for coeffs in kernel]
    r = data[selected]
    tests = [(parse(row["S"]), F(row["weight"])) for row in r["tests"]]
    require(all(s == trans(s) and w > 0 for s, w in tests), "symmetric positive tests")
    if selected == "I_universal":
        require(tests == [(v["identity"](), F(1))], "I tester binding")
    if selected == "Q_universal":
        require(tests == [(q, F(1))], "Q tester binding")
    outputs = [lyap(a0, s) for s, _ in tests]
    ds = [[lyap(a, s) for s, _ in tests] for a in directions]
    gram = [
        [
            sum(w * inner(x, y) for x, y, (_, w) in zip(row, other, tests, strict=True))
            for other in ds
        ]
        for row in ds
    ]
    linear = [
        sum(w * inner(x, o) for x, o, (_, w) in zip(row, outputs, tests, strict=True)) for row in ds
    ]
    require(parse(r["normal_gram"]) == gram, "normal Gram binding")
    require(list(map(F, r["linear"])) == linear, "linear term binding")
    z = list(map(F, r["optimizer_z"]))
    require(len(z) == 9, "optimizer dimension")
    require(
        all(
            sum(x * y for x, y in zip(row, z, strict=True)) + ell == 0
            for row, ell in zip(gram, linear, strict=True)
        ),
        "normal stationarity",
    )
    a = a0
    for direction, zi in zip(directions, z, strict=True):
        a = plus(a, direction, zi)
    require(parse(r["minimizer_A"]) == a, "minimizer binding")
    require(plus(mult(a, k), mult(k, trans(a))) == y, "original pair first")
    require(plus(mult(trans(a), y), mult(y, a)) == k, "original pair second")
    objective = sum(w * energy(lyap(a, s)) for s, w in tests)
    denominator = sum(w * energy(s) for s, w in tests)
    require(denominator > 0, "positive denominator")
    require(
        F(r["minimum_objective"]) == objective and F(r["denominator"]) == denominator,
        "objective and denominator",
    )
    bound = objective / denominator
    require(F(r["exact_s_squared_lower_bound"]) == bound, "final bound")
    require(r["excluding"] == (bound >= 1), "decision")
    return {"test": selected, "s_squared_lower": str(bound), "excludes_s_below_one": bound >= 1}


def main():
    source = BASE / "inventor_testers.json"
    data = json.loads(source.read_text())
    old = json.loads((BASE / "inventor_minnorm.json").read_text())[0]
    names = [
        name
        for name, row in data.items()
        if isinstance(row, dict) and "exact_s_squared_lower_bound" in row
    ]
    results = [verify(data, old, name) for name in names]
    rejected = []
    for name in ["I_universal", "Q_universal", "HS_universal"]:
        for mutation in ["kernel", "optimizer", "bound"]:
            bad = copy.deepcopy(data)
            if mutation == "kernel":
                bad["kernel_H_coefficients"][0][0] = str(F(bad["kernel_H_coefficients"][0][0]) + 1)
            elif mutation == "optimizer":
                bad[name]["optimizer_z"][0] = str(F(bad[name]["optimizer_z"][0]) + 1)
            else:
                bad[name]["exact_s_squared_lower_bound"] = "0"
            try:
                verify(bad, old, name)
            except ValueError as exc:
                rejected.append({"test": name, "mutation": mutation, "reason": str(exc)})
            else:
                raise ValueError("accepted mutation")
    out = {
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "producer_imports": False,
        "results": results,
        "negative_controls": rejected,
    }
    (BASE / "critic_tester_results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"verified": results, "mutations_rejected": len(rejected)}, indent=2))


if __name__ == "__main__":
    main()
