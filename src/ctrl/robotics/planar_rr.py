"""Rigid-body model of the planar RR arm, linear in five inertial parameters.

Geometry follows ``ControlsLean/Robotics/PlanarArm.lean`` (``fk``): absolute shoulder angle
``q1``, relative elbow angle ``q2``, so link 2 points along ``q1 + q2``. Gravity ``g0`` acts
along ``-y`` of ``fk``. PlanarArm.lean proves kinematics only; the dynamics below are the
standard Lagrangian model of that geometry and are checked by tests here, not by Lean.

Parameters (see :func:`params_from_physical`)::

    theta = (I1 + m1 lc1^2 + I2 + m2 (l1^2 + lc2^2),  m2 l1 lc2,  I2 + m2 lc2^2,
             m1 lc1 + m2 l1,  m2 lc2)

A point payload ``m_p`` at the tip adds ``m_p * (l1^2 + l2^2, l1 l2, l2^2, l1, l2)``.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

G0 = 9.81
NP = 5


@dataclass(frozen=True)
class ArmPhysical:
    """Two uniform-ish links plus an optional tip payload (SI units)."""

    l1: float = 1.0
    l2: float = 0.8
    m1: float = 2.0
    m2: float = 1.5
    lc1: float = 0.5
    lc2: float = 0.4
    I1: float = 2.0 * 1.0**2 / 12.0
    I2: float = 1.5 * 0.8**2 / 12.0
    payload: float = 0.0


def params_from_physical(p: ArmPhysical) -> np.ndarray:
    th = np.array(
        [
            p.I1 + p.m1 * p.lc1**2 + p.I2 + p.m2 * (p.l1**2 + p.lc2**2),
            p.m2 * p.l1 * p.lc2,
            p.I2 + p.m2 * p.lc2**2,
            p.m1 * p.lc1 + p.m2 * p.l1,
            p.m2 * p.lc2,
        ]
    )
    return th + p.payload * payload_direction(p)


def payload_direction(p: ArmPhysical) -> np.ndarray:
    """d theta / d m_p for a point mass at the tip of link 2."""
    return np.array([p.l1**2 + p.l2**2, p.l1 * p.l2, p.l2**2, p.l1, p.l2])


def mass_matrix(theta: np.ndarray, q: np.ndarray) -> np.ndarray:
    c2 = np.cos(q[1])
    m12 = theta[2] + theta[1] * c2
    return np.array([[theta[0] + 2.0 * theta[1] * c2, m12], [m12, theta[2]]])


def mass_matrix_dot(theta: np.ndarray, q: np.ndarray, dq: np.ndarray) -> np.ndarray:
    d = -theta[1] * np.sin(q[1]) * dq[1]
    return np.array([[2.0 * d, d], [d, 0.0]])


def coriolis(theta: np.ndarray, q: np.ndarray, dq: np.ndarray) -> np.ndarray:
    """Christoffel-form C(q, dq); with it, Mdot - 2C is skew-symmetric."""
    h = theta[1] * np.sin(q[1])
    return h * np.array([[-dq[1], -(dq[0] + dq[1])], [dq[0], 0.0]])


def gravity(theta: np.ndarray, q: np.ndarray, g0: float = G0) -> np.ndarray:
    c12 = np.cos(q[0] + q[1])
    return g0 * np.array([theta[3] * np.cos(q[0]) + theta[4] * c12, theta[4] * c12])


def regressor(
    q: np.ndarray, dq: np.ndarray, v: np.ndarray, a: np.ndarray, g0: float = G0
) -> np.ndarray:
    """Y(q, dq, v, a) with Y theta = M(q) a + C(q, dq) v + g(q) for every theta."""
    c1, c2, s2, c12 = np.cos(q[0]), np.cos(q[1]), np.sin(q[1]), np.cos(q[0] + q[1])
    return np.array(
        [
            [
                a[0],
                c2 * (2.0 * a[0] + a[1]) - s2 * (dq[1] * v[0] + (dq[0] + dq[1]) * v[1]),
                a[1],
                g0 * c1,
                g0 * c12,
            ],
            [0.0, c2 * a[0] + s2 * dq[0] * v[0], a[0] + a[1], 0.0, g0 * c12],
        ]
    )


def forward_dynamics(
    theta: np.ndarray, q: np.ndarray, dq: np.ndarray, tau: np.ndarray, g0: float = G0
) -> np.ndarray:
    """ddq solving M ddq + C dq + g = tau."""
    rhs = tau - coriolis(theta, q, dq) @ dq - gravity(theta, q, g0)
    return np.linalg.solve(mass_matrix(theta, q), rhs)
