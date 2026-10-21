"""Numerical screen of a causal derivative blend, original physical coordinates.

Uses current reference derivatives and a nominal plant, never the unknown disturbance.
This is an architecture change, not a certificate for the old low-pass controller.
Run: uv run --with numpy --with scipy python <this file>
"""

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.linalg import expm

HERE = Path(__file__).resolve().parent
SOURCE = Path(
    "/Users/mike/Documents/Codex/2026-10-16/okay-spend-30-or-40-minutes/"
    "research/pods/2026-10-17/controls/causal-stop-05/builder/reference.json"
)


def derivative(coeff):
    return [i * c for i, c in enumerate(coeff)][1:] or [0.0]


def run(alpha, rate=80.0, disturbance=0.01, nominal_rate=80.0, dt=0.00025):
    """alpha=None denotes unchanged algebraic direct control."""
    state = np.zeros(4)
    peaks = {"position_error_m": 0.0, "actual_jerk": 0.0, "command_rate": 0.0}
    variation, previous_u, initial, last = 0.0, None, None, None
    joins = []
    k, lam = 1.0 / 96, 20.0
    for phase in json.loads(SOURCE.read_text()):
        coeff = [float(Fraction(c)) for c in phase["position_coefficients_local_time"]]
        polynomials = [coeff]
        for _ in range(4):
            polynomials.append(derivative(polynomials[-1]))
        matrix = np.zeros((11, 11))
        matrix[0, 1] = matrix[1, 2] = 1.0
        matrix[2, 2], matrix[2, 3], matrix[2, 4] = -rate, rate, rate * disturbance
        forcing = np.zeros(7)
        if alpha is None:
            matrix[2, :4] = [-rate * 800, -rate * 60, -rate * 1.5, 0]
            for poly, weight in zip(polynomials, [800, 60, 1.5, k, 0], strict=True):
                forcing[: len(poly)] += rate * weight * np.array(poly)
            matrix[2, 4:] += forcing
        else:
            matrix[3, :4] = [
                -lam * 800,
                -lam * 60 - alpha * 800,
                -lam * 0.5 + alpha * (-60 + nominal_rate * 0.5),
                -lam - alpha * nominal_rate * 0.5,
            ]
            for poly, weight in zip(
                polynomials,
                [
                    800 * lam,
                    60 * lam + 800 * alpha,
                    1.5 * lam + 60 * alpha,
                    k * lam + 1 + 0.5 * alpha,
                    k * alpha,
                ],
                strict=True,
            ):
                forcing[: len(poly)] += weight * np.array(poly)
            matrix[3, 4:] = forcing
        for power in range(1, 7):
            matrix[4 + power, 3 + power] = power
        start, end = float(Fraction(phase["start"])), float(Fraction(phase["end"]))
        nsteps = int(np.ceil((end - start) / dt))
        step = (end - start) / nsteps
        propagator = expm(matrix * step)
        augmented = np.r_[state, 1.0, np.zeros(6)]
        for i in range(nsteps + 1):
            tau = i * step
            q, qv, qa, jerk, snap = [np.polynomial.polynomial.polyval(tau, p) for p in polynomials]
            x, v, a, u = augmented[:4]
            vd = 1.5 * qa + 800 * (q - x) + 60 * (qv - v) - 0.5 * a + k * jerk
            if alpha is None:
                u = vd
            actual_jerk = rate * (u + disturbance - a)
            nominal_jerk = nominal_rate * (u - a)
            vd_prime = 1.5 * jerk + 800 * (qv - v) + 60 * (qa - a)
            vd_prime += -0.5 * nominal_jerk + k * snap
            uprime = (
                vd_prime - 0.5 * (actual_jerk - nominal_jerk)
                if alpha is None
                else lam * (vd - u) + (1 - alpha) * jerk + alpha * vd_prime
            )
            row = dict(
                t=start + tau,
                x=x,
                v=v,
                a=a,
                u=u,
                q=q,
                error=x - q,
                actual_jerk=actual_jerk,
                command_rate=uprime,
            )
            if i == 0 and last:
                joins.append(max(abs(row[key] - last[key]) for key in ["x", "v", "a", "u", "q"]))
            for key, value in zip(peaks, [x - q, actual_jerk, uprime], strict=True):
                peaks[key] = max(peaks[key], abs(value))
            if previous_u is not None:
                variation += abs(u - previous_u)
            previous_u = u
            initial = initial or row
            if i < nsteps:
                augmented = propagator @ augmented
        state = augmented[:4].copy()
        last = row
    return dict(
        alpha=alpha,
        rate=rate,
        disturbance=disturbance,
        nominal_rate=nominal_rate,
        dt=dt,
        peaks=peaks,
        sampled_command_tv=variation,
        initial=initial,
        final=last,
        max_join_defect=max(joins),
    )


if __name__ == "__main__":
    cases = [run(alpha) for alpha in [None, 0, 0.25, 0.5, 0.75, 1]]
    result = dict(
        evidence="sampled numerical; no all-time bound",
        cases=cases,
        reference_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    )
    (HERE / "pm_bypass_results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            [dict(alpha=c["alpha"], peaks=c["peaks"], tv=c["sampled_command_tv"]) for c in cases],
            indent=2,
        )
    )
