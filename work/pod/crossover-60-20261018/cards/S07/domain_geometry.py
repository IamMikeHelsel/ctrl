"""Exact source-P geometry; no numerical optimization."""

import json
from fractions import Fraction as F
from pathlib import Path

P = [
    [F(38, 5), F(257, 25), F(5)],
    [F(257, 25), F(1319, 50), F(769, 50)],
    [F(5), F(769, 50), F(278, 25)],
]
A = [r[:] + [F(i == j) for j in range(3)] for i, r in enumerate(P)]
for i in range(3):
    pivot = A[i][i]
    A[i] = [v / pivot for v in A[i]]
    for j in range(3):
        if j != i:
            c = A[j][i]
            A[j] = [v - c * w for v, w in zip(A[j], A[i], strict=True)]
inv = [r[3:] for r in A]
c = [F(-1), F(-3), F(-2)]
y = [sum(row[j] * c[j] for j in range(3)) for row in inv]
kappa = sum(c[i] * y[i] for i in range(3))
sigma = inv[0][0]
# Rational active points on the minimum-energy request line: input(y*t)=kappa*t.
witness = [v * 2 / kappa for v in y]
energy = sum(witness[i] * P[i][j] * witness[j] for i in range(3) for j in range(3))
assert sum(c[i] * witness[i] for i in range(3)) == 2
assert energy == 4 / kappa < 12
result = {
    "P": [[str(v) for v in r] for r in P],
    "P_inverse": [[str(v) for v in r] for r in inv],
    "input_covector": list(map(str, c)),
    "P_inverse_c": list(map(str, y)),
    "kappa": str(kappa),
    "position_sigma": str(sigma),
    "max_input_squared_at_R12": str(12 * kappa),
    "max_position_squared_at_R12": str(12 * sigma),
    "active_intersection_threshold_R": str(1 / kappa),
    "quarter_sector_threshold_R": str(16 / kappa),
    "travel2_threshold_R": str(4 / sigma),
    "input2_min_energy_witness": list(map(str, witness)),
    "witness_energy": str(energy),
    "scope": "Exact ellipsoid geometry. Expanding dynamics certificate requires separate proof.",
}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))


def ldl(M):
    L = [[F(i == j) for j in range(3)] for i in range(3)]
    D = []
    for i in range(3):
        d = M[i][i] - sum(L[i][k] ** 2 * D[k] for k in range(i))
        D.append(d)
        for j in range(i + 1, 3):
            L[j][i] = (M[j][i] - sum(L[j][k] * L[i][k] * D[k] for k in range(i))) / d
    assert all(
        M[i][j] == sum(L[i][k] * D[k] * L[j][k] for k in range(3))
        for i in range(3)
        for j in range(3)
    )
    return L, D


residuals = []
for scalar, cov in [(kappa, c), (sigma, [F(1), F(0), F(0)])]:
    M = [[scalar * P[i][j] - cov[i] * cov[j] for j in range(3)] for i in range(3)]
    L, D = ldl(M)
    assert D[0] > 0 and D[1] > 0 and D[2] == 0
    residuals.append({"L": [[str(x) for x in row] for row in L], "D": list(map(str, D))})
result["residual_LDL"] = residuals
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")


def leanfrac(f):
    return f"({f.numerator}/{f.denominator}:ℝ)"


energy_text = "(38/5)*x^2+(1319/50)*v^2+(278/25)*a^2+2*(257/25)*x*v+10*x*a+2*(769/50)*v*a"
lines = [
    "import Mathlib.Tactic",
    "namespace S07Domain",
    f"noncomputable def V (x v a : ℝ) : ℝ := {energy_text}",
]
for name, scalar, _cov, res in zip(
    ["input", "position"], [kappa, sigma], [c, [F(1), F(0), F(0)]], residuals, strict=True
):
    L = [[F(x) for x in row] for row in res["L"]]
    D = [F(x) for x in res["D"]]
    linear = "(-x-3*v-2*a)" if name == "input" else "x"
    sq0 = f"(x+{leanfrac(L[1][0])}*v+{leanfrac(L[2][0])}*a)^2"
    sq1 = f"(v+{leanfrac(L[2][1])}*a)^2"
    lines += [
        f"theorem {name}_sos (x v a : ℝ) : {leanfrac(scalar)}*V x v a-{linear}^2 =",
        f"  {leanfrac(D[0])}*{sq0}+{leanfrac(D[1])}*{sq1} := by unfold V; ring",
        f"theorem {name}_bound (x v a : ℝ) : {linear}^2 ≤ {leanfrac(scalar)}*V x v a := by",
        f"  have h := {name}_sos x v a",
        f"  have h0 : 0 ≤ {leanfrac(D[0])}*{sq0} := mul_nonneg (by norm_num) (sq_nonneg _)",
        f"  have h1 : 0 ≤ {leanfrac(D[1])}*{sq1} := mul_nonneg (by norm_num) (sq_nonneg _)",
        "  linarith",
    ]
lines += [
    "theorem active_witness : V (15134/165339) (-50732/165339) (-96808/165339) = 44527328/4133475 ∧",
    "  -(15134/165339:ℝ)-3*(-50732/165339)-2*(-96808/165339)=2 ∧ (44527328/4133475:ℝ)<12 := by norm_num [V]",
    "theorem expanded_geometry (x v a : ℝ) (h : V x v a ≤ 44527328/3550075) :",
    "  x^2 ≤ 4 ∧ (-x-3*v-2*a)^2 ≤ 16 := by",
    "  have hp := position_bound x v a",
    "  have hu := input_bound x v a",
    "  constructor <;> nlinarith",
    "theorem expanded_budget : (13:ℝ)*(1/5+(5/451)⁻¹)*(1/100)^2 ≤ (5/451)*(44527328/3550075) := by norm_num",
    "end S07Domain",
]
for name in [
    "input_sos",
    "input_bound",
    "position_sos",
    "position_bound",
    "active_witness",
    "expanded_geometry",
    "expanded_budget",
]:
    lines.append(f"#print axioms S07Domain.{name}")
Path(__file__).with_name("domain_geometry.lean").write_text("\n".join(lines) + "\n")
