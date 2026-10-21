"""Independent physical-state integrations; numerical evidence, no enclosure."""

import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

HERE = Path(__file__).parent
H = 0.02
W = 0.0005


def physical(kappa, name, sigma=1.0, initial=(0.0, 0.0, 0.0), reset=False, cap=None):
    state = np.array(initial)
    ref = np.zeros(3)
    start = 0.0
    times, errors = [], []
    for duration, j in [(H, 10.0), (H, -10.0), (H, -10.0), (H, 10.0), (4.0, 0.0)]:

        def qr(t, start=start, ref=ref, j=j):
            dt = t - start
            return ref + np.array(
                [
                    ref[1] * dt + ref[2] * dt**2 / 2 + j * dt**3 / 6,
                    ref[2] * dt + j * dt**2 / 2,
                    j * dt,
                ]
            )

        def rhs(t, y, qr=qr, j=j):
            q = qr(t)
            e = y - q
            u = q[2] - 8 * sigma**2 * e[0] - 6 * sigma * e[1] - 0.5 * e[2] + kappa * j
            if cap is not None:
                u = min(cap, max(-cap, u))
            if name.startswith("fixed"):
                r = sigma * float(name[5:])
            else:
                phase = int(name[5:]) * math.pi / 2
                r = sigma * (10 - 2 * math.tanh(4 * math.cos(math.pi * t / (2 * H) + phase)))
            w = -W * (-math.expm1(-20 * t))
            return [y[1], y[2], r * (u + w - y[2])]

        if reset:
            state = ref.copy()
        mesh = np.linspace(start, start + duration, math.ceil(duration / 0.0005) + 1)
        sol = solve_ivp(
            rhs,
            (start, start + duration),
            state,
            method="RK45",
            rtol=2e-10,
            atol=2e-14,
            max_step=0.0005,
            t_eval=mesh,
        )
        assert sol.success
        err = sol.y[0] - np.array([qr(t)[0] for t in mesh])
        times.extend(mesh.tolist())
        errors.extend(err.tolist())
        state = sol.y[:, -1]
        ref = qr(start + duration)
        start += duration
    return np.array(times), np.array(errors)


fit = json.loads((HERE / "inventor_minimax.json").read_text())["fine"]["optimum"]
k = fit["c_seconds"]
rows = []
for name in ["fixed8", "fixed10", "fixed12", "phase0", "phase1", "phase2", "phase3"]:
    t, e = physical(k, name)
    expected = json.loads((HERE / "inventor_minimax.json").read_text())["fine"]["scores_m"][
        "tuned"
    ][name]
    rows.append(
        {
            "rate": name,
            "peak_m": float(max(abs(e))),
            "source_peak_m": expected,
            "difference_m": float(abs(max(abs(e)) - expected)),
            "terminal_m": float(e[-1]),
        }
    )
    assert abs(max(abs(e)) - expected) < 2e-10
# An affine combination at every common sample, including coefficient-independent nonzero IC.
t, e0 = physical(0.0, "fixed8", initial=(1e-5, -2e-5, 3e-5))
_, e1 = physical(0.1, "fixed8", initial=(1e-5, -2e-5, 3e-5))
_, em = physical(-0.03, "fixed8", initial=(1e-5, -2e-5, 3e-5))
affine_error = float(max(abs(em - (1.3 * e0 - 0.3 * e1))))
assert affine_error < 1e-12
_, er = physical(k, "fixed8", reset=True)
_, ef = physical(k, "fixed8")
reset_difference = float(max(abs(er - ef)))
assert reset_difference > 1e-5
# Same equation after saturation is a changed model, and the affine property fails.
_, s0 = physical(0.0, "fixed8", cap=0.05)
_, s1 = physical(0.1, "fixed8", cap=0.05)
_, sm = physical(0.05, "fixed8", cap=0.05)
saturation_error = float(max(abs(sm - (s0 + s1) / 2)))
assert saturation_error > 1e-5
# Dimensionless d=sigma*kappa; treating d as seconds at sigma10 changes response.
_, unit_ok = physical(0.01, "fixed8", sigma=10.0)
_, unit_bad = physical(0.1, "fixed8", sigma=10.0)
units_difference = float(max(abs(unit_ok - unit_bad)))
assert units_difference > 1e-5
# Floating data dual is algebraically checked; not an exact ODE/time certificate.
left, right = fit["active_lines"]
weight = fit["convex_dual_weight"]
slope = weight * left[4] + (1 - weight) * right[4]
lower = weight * left[3] + (1 - weight) * right[3]
assert 0 <= weight <= 1 and abs(slope) < 1e-15
assert abs(lower - fit["peak_m"]) < 1e-15
out = {
    "runtime": "uv --no-project --python /usr/local/bin/python3; scipy 1.16.2",
    "physical_state_replays": rows,
    "affine_nonzero_initial_max_difference_m": affine_error,
    "negative_controls": {
        "state_reset_difference_m": reset_difference,
        "saturation_affine_failure_m": saturation_error,
        "coefficient_units_difference_m": units_difference,
    },
    "floating_dual_slope": slope,
    "floating_dual_bound_m": lower,
    "scope": "Numerical RK45 physical equations, original reference and all seven declared rates. Independent from producer basis functions. No continuous-time or uncertainty-set enclosure.",
}
(HERE / "critic_physical.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
