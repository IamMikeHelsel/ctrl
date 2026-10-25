"""Energy-optimal septic rest-to-rest trajectories and clock-warp semantics.

Every public function is backed by a machine-checked theorem in
``Research.RobotEnergySmoothness`` or ``Research.WorldFrameTransport`` and supports both:
- ``float`` / ``numpy.ndarray`` (real-time / MuJoCo rollout mode), and
- ``fractions.Fraction`` (exact-Q certificate mode with zero floating-point rounding).
"""

from __future__ import annotations

from fractions import Fraction
from typing import TypeVar, overload

import numpy as np

from ctrl.robotics.registry import lean_theorem

Scalar = TypeVar("Scalar", float, Fraction, np.ndarray)


@overload
def septic_q(eta: Fraction, s: Fraction) -> Fraction: ...


@overload
def septic_q(eta: float, s: float | np.ndarray) -> float | np.ndarray: ...


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("qProfile", "septic_rest_to_rest_boundaries", "qProfile_hasDerivAt"),
    domain="trajectories",
    summary="Symmetric C^2 rest-to-rest degree-7 position profile q_eta(s).",
)
def septic_q(eta: Scalar, s: Scalar) -> Scalar:
    """Evaluate position profile q_eta(s) = 10 s^3 - 15 s^4 + 6 s^5 + eta s^3 (1-s)^3 (2s-1)."""
    return 10 * s**3 - 15 * s**4 + 6 * s**5 + eta * (s**3) * ((1 - s) ** 3) * (2 * s - 1)


@overload
def septic_v(eta: Fraction, s: Fraction) -> Fraction: ...


@overload
def septic_v(eta: float, s: float | np.ndarray) -> float | np.ndarray: ...


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("vProfile", "septic_rest_to_rest_boundaries", "vProfile_hasDerivAt"),
    domain="trajectories",
    summary="Exact first derivative q'_eta(s) of the symmetric septic trajectory.",
)
def septic_v(eta: Scalar, s: Scalar) -> Scalar:
    """Evaluate dimensionless velocity profile v_eta(s) = dq_eta/ds."""
    return (
        30 * s**2
        - 60 * s**3
        + 30 * s**4
        + eta * (-3 * s**2 + 20 * s**3 - 45 * s**4 + 42 * s**5 - 14 * s**6)
    )


@overload
def septic_a(eta: Fraction, s: Fraction) -> Fraction: ...


@overload
def septic_a(eta: float, s: float | np.ndarray) -> float | np.ndarray: ...


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("aProfile", "septic_rest_to_rest_boundaries", "aProfile_hasDerivAt"),
    domain="trajectories",
    summary="Exact second derivative q''_eta(s) of the symmetric septic trajectory.",
)
def septic_a(eta: Scalar, s: Scalar) -> Scalar:
    """Evaluate dimensionless acceleration profile a_eta(s) = d^2q_eta/ds^2."""
    return (
        60 * s
        - 180 * s**2
        + 120 * s**3
        + eta * (-6 * s + 60 * s**2 - 180 * s**3 + 210 * s**4 - 84 * s**5)
    )


@overload
def septic_j(eta: Fraction, s: Fraction) -> Fraction: ...


@overload
def septic_j(eta: float, s: float | np.ndarray) -> float | np.ndarray: ...


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("jProfile", "aProfile_hasDerivAt"),
    domain="trajectories",
    summary="Exact third derivative q'''_eta(s) of the symmetric septic trajectory.",
)
def septic_j(eta: Scalar, s: Scalar) -> Scalar:
    """Evaluate dimensionless jerk profile j_eta(s) = d^3q_eta/ds^3."""
    return (
        60
        - 360 * s
        + 360 * s**2
        + eta * (-6 + 120 * s - 540 * s**2 + 840 * s**3 - 420 * s**4)
    )


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("Iv", "Fv", "Fv_hasDerivAt", "exact_integral_quadratic_forms"),
    domain="trajectories",
    summary="Exact velocity L^2 energy integral I_v(eta) = (3/10010)(eta + 260/9)^2 + 350/297.",
)
def septic_velocity_integral(eta: float | Fraction) -> float | Fraction:
    """Return exact dimensionless velocity L^2 norm integral I_v(eta) = int_0^1 v_eta(s)^2 ds."""
    if isinstance(eta, Fraction):
        return Fraction(3, 10010) * (eta + Fraction(260, 9)) ** 2 + Fraction(350, 297)
    return (3.0 / 10010.0) * (eta + 260.0 / 9.0) ** 2 + (350.0 / 297.0)


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("Ia", "Fa", "Fa_hasDerivAt", "exact_integral_quadratic_forms"),
    domain="trajectories",
    summary="Exact acceleration L^2 energy integral I_a(eta) = (2/77)(eta + 11)^2 + 14.",
)
def septic_accel_integral(eta: float | Fraction) -> float | Fraction:
    """Return exact dimensionless acceleration L^2 norm integral I_a(eta) = int_0^1 a_eta(s)^2 ds."""
    if isinstance(eta, Fraction):
        return Fraction(2, 77) * (eta + Fraction(11, 1)) ** 2 + Fraction(14, 1)
    return (2.0 / 77.0) * (eta + 11.0) ** 2 + 14.0


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("Ij", "Fj", "Fj_hasDerivAt", "exact_integral_quadratic_forms", "min_jerk_uniquely_minimizes_Ij"),
    domain="trajectories",
    summary="Exact jerk L^2 smoothness integral I_j(eta) = 4 eta^2 + 720.",
)
def septic_jerk_integral(eta: float | Fraction) -> float | Fraction:
    """Return exact dimensionless jerk L^2 norm integral I_j(eta) = int_0^1 j_eta(s)^2 ds."""
    if isinstance(eta, Fraction):
        return 4 * eta**2 + Fraction(720, 1)
    return 4.0 * (eta**2) + 720.0


@lean_theorem(
    "Research.RobotEnergySmoothness",
    (
        "electromechanicalEnergy",
        "rest_to_rest_cross_power_zero",
        "dual_energy_reduction_on_interval",
        "exact_savings_at_minus_eleven",
        "min_jerk_strictly_pareto_dominated",
    ),
    domain="trajectories",
    summary="Exact electromechanical energy (I^2 R Joule + viscous dissipation) on rest-to-rest motion.",
)
def electromechanical_energy(
    m: float | Fraction,
    b: float | Fraction,
    r_elec: float | Fraction,
    k_t: float | Fraction,
    displacement: float | Fraction,
    duration: float | Fraction,
    eta: float | Fraction,
) -> float | Fraction:
    """Compute exact rest-to-rest actuator electromechanical energy E_total(eta)."""
    if duration <= 0:
        raise ValueError("duration T must be strictly positive (T > 0).")
    if k_t == 0:
        raise ValueError("torque constant k_t must be non-zero (Kt != 0).")
    ia = septic_accel_integral(eta)
    iv = septic_velocity_integral(eta)
    coeff_a = (r_elec * (m**2)) / ((k_t**2) * (duration**3))
    coeff_v = ((r_elec * (b**2)) / (k_t**2) + b) / duration
    return (displacement**2) * (coeff_a * ia + coeff_v * iv)


@lean_theorem(
    "Research.RobotEnergySmoothness",
    ("electromechanicalEnergy", "exact_integral_quadratic_forms", "min_jerk_strictly_pareto_dominated"),
    domain="trajectories",
    summary="Hardware-matched optimal septic parameter eta* minimizing total electromechanical energy.",
)
def optimal_septic_eta(
    m: float | Fraction,
    b: float | Fraction,
    r_elec: float | Fraction,
    k_t: float | Fraction,
    duration: float | Fraction,
    *,
    clamp_monotone: bool = True,
) -> float | Fraction:
    """Compute the quadratic minimizer eta* of E_total(eta), optionally clamped to [-11, 0].

    Since E_total(eta) = D^2 * (c_a I_a(eta) + c_v I_v(eta)) with
    I_a'(eta) = (4/77)(eta + 11) and I_v'(eta) = (6/10010)(eta + 260/9),
    the exact unconstrained minimizer is a convex combination of -11 and -260/9.
    Clamping to [-11, 0] restricts eta* to the Pareto-improving interval between the
    minimum-acceleration profile (eta = -11, within the monotone velocity range [-15, 9])
    and the classical minimum-jerk quintic profile (eta = 0), capturing the full 18.33%
    inertial Joule reduction at eta = -11.
    """
    if duration <= 0:
        raise ValueError("duration T must be strictly positive (T > 0).")
    if k_t == 0:
        raise ValueError("torque constant k_t must be non-zero (Kt != 0).")
    use_frac = all(isinstance(x, Fraction) for x in (m, b, r_elec, k_t, duration))
    if use_frac:
        mf, bf, rf, ktf, tf = (
            Fraction(m),
            Fraction(b),
            Fraction(r_elec),
            Fraction(k_t),
            Fraction(duration),
        )
        ca = (rf * mf * mf) / (ktf * ktf * (tf**3))
        cv = ((rf * bf * bf) / (ktf * ktf) + bf) / tf
        wa = ca * Fraction(2, 77)
        wv = cv * Fraction(3, 10010)
        eta_star = -(wa * Fraction(11, 1) + wv * Fraction(260, 9)) / (wa + wv)
        if clamp_monotone:
            return max(Fraction(-11, 1), min(Fraction(0, 1), eta_star))
        return eta_star

    ca_f = (float(r_elec) * float(m) ** 2) / (float(k_t) ** 2 * float(duration) ** 3)
    cv_f = ((float(r_elec) * float(b) ** 2) / float(k_t) ** 2 + float(b)) / float(duration)
    wa_f = ca_f * (2.0 / 77.0)
    wv_f = cv_f * (3.0 / 10010.0)
    eta_star_f = -(wa_f * 11.0 + wv_f * (260.0 / 9.0)) / (wa_f + wv_f)
    if clamp_monotone:
        return float(np.clip(eta_star_f, -11.0, 0.0))
    return float(eta_star_f)


@lean_theorem(
    "Research.WorldFrameTransport",
    (
        "timewarp_velocity_hasDerivAt",
        "timewarp_accel_hasDerivAt",
        "timewarp_jerk_hasDerivAt",
        "splineBranch_hasDerivAt_zero",
        "clock_slew_breaks_spline_differentiability",
    ),
    domain="trajectories",
    summary="Exact 1st/2nd/3rd-order clock-warp derivative chain rules and piecewise slew velocity jump.",
)
def timewarp_derivatives(
    dq: float | Fraction,
    ddq: float | Fraction,
    dddq: float | Fraction,
    dtau: float | Fraction,
    ddtau: float | Fraction,
    dddtau: float | Fraction,
) -> tuple[float | Fraction, float | Fraction, float | Fraction]:
    """Compute world-time (velocity, acceleration, jerk) of q(tau(t)) via the verified chain rule."""
    v = dtau * dq
    a = ddtau * dq + (dtau**2) * ddq
    j = dddtau * dq + 3 * dtau * ddtau * ddq + (dtau**3) * dddq
    return v, a, j
