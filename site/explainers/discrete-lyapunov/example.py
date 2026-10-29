"""Numbers shared by the diagram and both animations. Single source of truth.

2D example: A has spectral radius 0.9 but operator norm about 1.17, so the Euclidean norm
of the state can grow on a step. P solves the Stein equation A^T P A - P = -I, so
V(x) = x^T P x drops on every step by at least a fixed factor.
The exact SymPy artifact supplies A and P; NumPy values below are for plotting.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np

ARTIFACT = json.loads((Path(__file__).resolve().parents[1] / "lab/results.json").read_text())
EXACT = next(row for row in ARTIFACT["experiments"] if row["id"] == "lyapunov")

# Scalar example.
A_SCALAR = 0.8
A_SCALAR_BAD = 1.1

# Planar example.
A = np.array([[float(Fraction(t)) for t in row] for row in EXACT["A"]])
X0 = np.array([1.0, 0.0])
STEPS = 14


P = np.array([[float(Fraction(t)) for t in row] for row in EXACT["P"]])


def V(x: np.ndarray) -> float:
    return float(x @ P @ x)


def trajectory(x0: np.ndarray = X0, steps: int = STEPS) -> np.ndarray:
    xs = [x0]
    for _ in range(steps):
        xs.append(A @ xs[-1])
    return np.array(xs)


def contraction_factor() -> float:
    """Exact worst-case ratio V(Ax)/V(x): largest eigenvalue of P^{-1/2} A^T P A P^{-1/2}."""
    L = np.linalg.cholesky(P)
    Li = np.linalg.inv(L)
    return float(max(np.linalg.eigvalsh(Li @ A.T @ P @ A @ Li.T)))


def level_set(v: float, n: int = 240) -> np.ndarray:
    """Points of the ellipse {x : x^T P x = v}."""
    L = np.linalg.cholesky(P)  # P = L L^T, so x = sqrt(v) L^{-T} u
    t = np.linspace(0, 2 * np.pi, n)
    u = np.stack([np.cos(t), np.sin(t)])
    return (np.sqrt(v) * np.linalg.solve(L.T, u)).T


def lean_proof_rate() -> tuple[float, float]:
    """The rate the Lean proof builds: rho = 1 - c_Q / C_P, with c_Q and C_P taken over the
    sup-norm unit sphere (Mathlib's default norm on n -> R). Here Q = I, so c_Q = 1 at a
    coordinate vector, and C_P = max of x^T P x over the square's corners (P is PD here)."""
    corners = [np.array([a, b]) for a in (1.0, -1.0) for b in (1.0, -1.0)]
    c_q = 1.0
    c_p = max(float(x @ P @ x) for x in corners)
    return c_p, 1 - c_q / c_p


RHO = contraction_factor()
SPECTRAL_RADIUS = float(max(abs(np.linalg.eigvals(A))))
OP_NORM = float(np.linalg.norm(A, 2))

if __name__ == "__main__":
    np.set_printoptions(precision=4, suppress=True)
    print("Exact rational P:", EXACT["P"])
    print("Exact Stein residual checks:", [c["status"] for c in EXACT["checks"]])
    print("P =\n", P)
    print("P - A^T P A =\n", P - A.T @ P @ A)
    print(f"spectral radius {SPECTRAL_RADIUS:.4f}, ||A||_2 {OP_NORM:.4f}, rho {RHO:.4f}")
    c_p, rho_lean = lean_proof_rate()
    print(f"Lean proof (sup norm): C_P {c_p:.2f}, rho {rho_lean:.4f}")
    for k, x in enumerate(trajectory()):
        print(k, np.round(x, 3), f"|x|={np.linalg.norm(x):.3f}", f"V={V(x):.3f}")
