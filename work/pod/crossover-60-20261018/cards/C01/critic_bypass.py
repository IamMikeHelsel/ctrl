"""Independent physical DOP853 check, no producer imports."""

import json
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

BASE = Path(__file__).parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)
PHASES = json.loads(SOURCE.read_text())


def replay(alpha, reset=False, coefficient_mutation=False):
    state = np.zeros(4)
    peaks = np.zeros(3)
    variation, previous = 0.0, None
    for number, phase in enumerate(PHASES):
        start, end = [float(F(phase[k])) for k in ["start", "end"]]
        polys = [[float(F(c)) for c in phase["position_coefficients_local_time"]]]
        for _ in range(4):
            polys.append([i * c for i, c in enumerate(polys[-1])][1:] or [0.0])

        def output(time, z, polys=polys, start=start):
            q, qv, qa, j, snap = [np.polynomial.polynomial.polyval(time - start, p) for p in polys]
            x, v, a = z[:3]
            e, ev, ea = x - q, v - qv, a - qa
            desired = qa - 800 * e - 60 * ev - 0.5 * ea + j / 96
            u = desired if alpha is None else z[3]
            actual = 80 * (u + 0.01 - a)
            nominal = 80 * (u - a)
            desired_rate = (
                j
                - 800 * ev
                - 60 * ea
                - 0.5 * ((actual if alpha is None else nominal) - j)
                + snap / 96
            )
            if coefficient_mutation:
                desired_rate += 800 * ev
            uprime = (
                desired_rate
                if alpha is None
                else 20 * (desired - u) + (1 - alpha) * j + alpha * desired_rate
            )
            return e, actual, uprime, u

        def rhs(time, z, output=output):
            _, actual, uprime, _ = output(time, z)
            return [z[1], z[2], actual, 0 if alpha is None else uprime]

        if reset and number:
            state[3] = 0
        sol = solve_ivp(
            rhs,
            (start, end),
            state,
            method="DOP853",
            rtol=1e-11,
            atol=1e-13,
            max_step=0.001,
            dense_output=True,
        )
        if not sol.success:
            raise ValueError(sol.message)
        n = int(np.ceil((end - start) / 0.00025))
        for t in np.linspace(start, end, n + 1):
            values = output(t, sol.sol(t))
            peaks = np.maximum(peaks, np.abs(values[:3]))
            if previous is not None:
                variation += abs(values[3] - previous)
            previous = values[3]
        state = sol.y[:, -1]
    return dict(peaks=peaks.tolist(), tv=variation, final=state.tolist())


saved = json.loads((BASE / "pm_bypass_results.json").read_text())["cases"]
results = []
for row in saved:
    check = replay(row["alpha"])
    expected = list(row["peaks"].values()) + [row["sampled_command_tv"]]
    actual = check["peaks"] + [check["tv"]]
    differences = [abs(a - b) for a, b in zip(actual, expected, strict=False)]
    if max(differences) > 1e-7:
        raise ValueError(differences)
    results.append(dict(alpha=row["alpha"], maximum_difference=max(differences), result=check))
base = replay(0.5)
negatives = []
for mutation in ["reset", "coefficient_mutation"]:
    damaged = replay(0.5, **{mutation: True})
    mismatch = max(
        abs(a - b)
        for a, b in zip(
            base["peaks"] + [base["tv"]], damaged["peaks"] + [damaged["tv"]], strict=False
        )
    )
    if mismatch < 1e-3:
        raise ValueError("negative not discriminated")
    negatives.append(dict(mutation=mutation, mismatch=mismatch, result=damaged))
output = dict(
    cases=results,
    negative_controls=negatives,
    evidence="independent numerical integration; not all-time proof",
)
(BASE / "critic_bypass_results.json").write_text(json.dumps(output, indent=2) + "\n")
print(json.dumps(output, indent=2))
