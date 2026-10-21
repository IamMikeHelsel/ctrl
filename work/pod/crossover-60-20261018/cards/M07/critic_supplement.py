"""Independent bit-mask left kernel and finite-covector exact determinant tests."""

import json
import runpy
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).resolve().parent
op = runpy.run_path(str(P / "critic_operator.py"))
arith = runpy.run_path(str(P / "critic_symbol.py"))
B = op["B"]
image = op["image"]
kernel = []
nonzero = []
for index, x in enumerate(B["L3"]):
    outputs = image("L3", x, [1] * 10)
    mask = next(iter(x))
    if not (mask & 1):
        assert all(not a for a in outputs)
        kernel.append(index + 8)
    else:
        assert any(outputs)
        nonzero.append(index + 8)
assert len(kernel) == 35 and len(nonzero) == 21
base = F(arith["results"][0]["exact_determinant"])
results = []
saved = {r["covector"]: r for r in json.loads((P / "pm_covector.json").read_text())}
for name, v, norm2 in [
    ("e2", {2: F(1)}, 1),
    ("e1_plus_e2", {1: F(1), 2: F(1)}, 2),
    ("minus_e1", {1: F(-1)}, 1),
]:
    A = []
    for group in ("L1", "L3", "Y2", "Y4p"):
        for x in B[group]:
            outputs = image(group, x, [1, 1, 1, 1, 0, 1, 1, 1, 1, 1], v)
            row = [
                2 * sum(a * t.get(k, F(0)) for k, a in output.items())
                for output, target in zip(outputs, ("L4p", "Y3", "L2", "Y1"), strict=True)
                for t in B[target]
            ]
            A.append({i: c for i, c in enumerate(row) if c})
    groups = arith["components"](A, 448)
    rs = []
    cs = []
    D = F(1)
    for rr, cc in groups:
        assert len(rr) == len(cc)
        local = [{j: A[i].get(c, F(0)) for j, c in enumerate(cc) if A[i].get(c, 0)} for i in rr]
        _, p, d = arith["eliminate"](local, len(cc))
        D *= d
        rs += rr
        cs += cc
    D *= arith["parity"](rs) * arith["parity"](cs)
    assert D == base * norm2**224 == F(saved[name]["determinant"])
    results.append(
        {
            "covector": name,
            "exact_determinant": str(D),
            "matches_root_and_norm_prediction": True,
            "largest_component": max(len(r) for r, c in groups),
        }
    )
    print(name, "independently rebuilt and exact determinant matched", flush=True)
out = {
    "A6_zero_source_rows": kernel,
    "A6_nonzero_L3_rows": nonzero,
    "left_kernel_dimension": 35,
    "kernel_scope": "All four projected bit-mask forms vanish, not only pairings. Thirty-five standard L3 basis blades avoidingw1 give independent source vectors; exact rank413 establishes completeness of this kernel for the reconstructed map.",
    "covector_tests": results,
    "independence": "Own bit-mask operator and rational Gauss-Jordan; shared declared provisional source/target bases only.",
    "limitation": "Finite covector tests do not prove global covariance or ellipticity.",
}
(P / "critic_supplement.json").write_text(json.dumps(out, indent=2) + "\n")
