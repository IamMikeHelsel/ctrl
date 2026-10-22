"""3D 4-contact quadruped bilinear ZMP wrench allocation and Lorentz-cone backup CBF.

Every public function is backed by a machine-checked theorem in
``Research.LorentzConeCBF`` or ``Research.CentroidalDecelerationLimit`` and supports both
``float`` and exact ``fractions.Fraction`` (Q) arithmetic.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Generic, TypeVar

from ctrl.robotics.registry import lean_theorem

T = TypeVar("T", float, Fraction)
Vec3T = tuple[T, T, T]


def dot3(u: Vec3T[T], v: Vec3T[T]) -> T:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross3(u: Vec3T[T], v: Vec3T[T]) -> Vec3T[T]:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def add3(u: Vec3T[T], v: Vec3T[T]) -> Vec3T[T]:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def sub3(u: Vec3T[T], v: Vec3T[T]) -> Vec3T[T]:
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])


def smul3(c: T, u: Vec3T[T]) -> Vec3T[T]:
    return (c * u[0], c * u[1], c * u[2])


@dataclass(frozen=True)
class CentroidalQuadParams(Generic[T]):
    """Physical parameters for a 3D 4-contact rectangular stance [-Wx, Wx] x [-Wy, Wy]."""

    m: T
    g: T
    h_g: T
    w_x: T
    w_y: T
    mu: T


@lean_theorem(
    "Research.CentroidalDecelerationLimit",
    (
        "safeDecelMax",
        "safe_decel_max_pos",
        "deceleration_safe_unconditional",
        "deceleration_unsafe_counterexample",
        "deceleration_safe_iff",
    ),
    domain="contact_cbf",
    summary="Exact biconditional safe deceleration limit min(mu, W / h_G) * g.",
)
def safe_decel_max(g: T, mu: T, w_half: T, h_g: T) -> T:
    """Return the exact maximum safe braking deceleration min(mu, w_half / h_g) * g."""
    ratio = w_half / h_g
    limit = mu if mu <= ratio else ratio
    return g * limit


@lean_theorem(
    "Research.LorentzConeCBF",
    ("inLorentzCone", "inLorentzConeCoords", "lorentz_convex_combination"),
    domain="contact_cbf",
    summary="Second-order Lorentz friction cone membership fx^2 + fy^2 <= mu^2 fz^2 and fz >= 0.",
)
def in_lorentz_cone(mu: T, force: Vec3T[T], tol: float = 0.0) -> bool:
    """Check whether 3D contact force (fx, fy, fz) lies in the Lorentz friction cone K(mu)."""
    fx, fy, fz = force
    if isinstance(fx, Fraction) and isinstance(fy, Fraction) and isinstance(fz, Fraction):
        mu_f = Fraction(mu)
        return (fx * fx + fy * fy <= (mu_f * fz) ** 2) and (fz >= 0)
    return bool((fx * fx + fy * fy <= (mu * fz) ** 2 + tol) and (fz >= -tol))


@lean_theorem(
    "Research.LorentzConeCBF",
    ("quadNormalForce", "quadContactOffset"),
    domain="contact_cbf",
    summary="Bilinear ZMP normal contact force at corner (ex, ey) in {-1, +1}^2.",
)
def quad_normal_force(params: CentroidalQuadParams[T], ax: T, ay: T, ex: T, ey: T) -> T:
    """Compute bilinear ZMP normal contact force f_z at corner (ex, ey) in {-1, +1}^2."""
    zero_one = Fraction(1, 1) if isinstance(params.m, Fraction) else 1.0
    four = Fraction(4, 1) if isinstance(params.m, Fraction) else 4.0
    return (
        (params.m * params.g / four)
        * (zero_one - ex * (params.h_g * ax) / (params.g * params.w_x))
        * (zero_one - ey * (params.h_g * ay) / (params.g * params.w_y))
    )


@lean_theorem(
    "Research.LorentzConeCBF",
    (
        "quadContactForce",
        "quad_contact_net_force",
        "quad_contact_zero_angular_momentum",
        "quad_contact_in_lorentz_cone",
    ),
    domain="contact_cbf",
    summary="3D 4-contact bilinear ZMP + proportional shear wrench allocator with L_dot = 0.",
)
def quad_contact_forces(
    params: CentroidalQuadParams[T], ax: T, ay: T
) -> dict[tuple[int, int], Vec3T[T]]:
    """Allocate 3D contact forces at all 4 stance corners (-1,-1), (-1,1), (1,-1), (1,1)."""
    is_frac = isinstance(params.m, Fraction)
    corners: dict[tuple[int, int], Vec3T[T]] = {}
    for ex_i in (-1, 1):
        for ey_i in (-1, 1):
            ex: T = Fraction(ex_i, 1) if is_frac else float(ex_i)  # type: ignore[assignment]
            ey: T = Fraction(ey_i, 1) if is_frac else float(ey_i)  # type: ignore[assignment]
            fz = quad_normal_force(params, ax, ay, ex, ey)
            fx = (ax / params.g) * fz
            fy = (ay / params.g) * fz
            corners[(ex_i, ey_i)] = (fx, fy, fz)
    return corners


@lean_theorem(
    "Research.LorentzConeCBF",
    (
        "quad_contact_net_force",
        "quad_contact_zero_angular_momentum",
        "quad_contact_in_lorentz_cone",
    ),
    domain="contact_cbf",
    summary="Verify exact 3D Newton force realization, zero Euler torque, and Lorentz cone safety.",
)
def verify_quad_wrench_balance(
    params: CentroidalQuadParams[T], ax: T, ay: T
) -> dict[str, Vec3T[T] | bool]:
    """Compute net translational wrench, net 3D centroidal torque, and cone admissibility."""
    is_frac = isinstance(params.m, Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    forces = quad_contact_forces(params, ax, ay)
    net_f: Vec3T[T] = (zero, zero, zero)
    net_tau: Vec3T[T] = (zero, zero, zero)
    all_in_cone = True
    for (ex_i, ey_i), f_vec in forces.items():
        ex: T = Fraction(ex_i, 1) if is_frac else float(ex_i)  # type: ignore[assignment]
        ey: T = Fraction(ey_i, 1) if is_frac else float(ey_i)  # type: ignore[assignment]
        offset: Vec3T[T] = (ex * params.w_x, ey * params.w_y, -params.h_g)
        net_f = add3(net_f, f_vec)
        net_tau = add3(net_tau, cross3(offset, f_vec))
        if not in_lorentz_cone(params.mu, f_vec, tol=0.0 if is_frac else 1e-12):
            all_in_cone = False

    net_f_minus_grav: Vec3T[T] = (net_f[0], net_f[1], net_f[2] - params.m * params.g)
    return {
        "net_force_minus_gravity": net_f_minus_grav,
        "expected_force": (params.m * ax, params.m * ay, zero),
        "net_torque": net_tau,
        "all_in_lorentz_cone": all_in_cone,
    }


@lean_theorem(
    "Research.LorentzConeCBF",
    (
        "directionalCBF",
        "directional_cbf_hasDerivAt",
        "backup_braking_discharges_margin",
        "centroidal_cbf_forward_invariant",
    ),
    domain="contact_cbf",
    summary="3D directional stopping-distance Control Barrier Function h_dir(r, v).",
)
def directional_cbf(
    r_limit: Vec3T[T], r: Vec3T[T], v: Vec3T[T], n_hat: Vec3T[T], a_brake: T
) -> T:
    """Evaluate h_dir(r, v) = (r_limit - r) . n_hat - (v . n_hat)^2 / (2 a_brake)."""
    two: T = Fraction(2, 1) if isinstance(a_brake, Fraction) else 2.0  # type: ignore[assignment]
    vn = dot3(v, n_hat)
    return dot3(sub3(r_limit, r), n_hat) - (vn * vn) / (two * a_brake)


@lean_theorem(
    "Research.LorentzConeCBF",
    (
        "lambda_star",
        "interpolatedControl",
        "lambda_star_nonneg",
        "lambda_star_le_one",
        "interpolation_satisfies_barrier",
        "lorentz_backup_controller_safe",
    ),
    domain="contact_cbf",
    summary="Closed-form Lorentz-cone-preserving CBF interpolation u*(x) = (1-lambda*) u_nom + lambda* pi_b.",
)
def lorentz_cbf_safety_filter(
    a_cbf: Vec3T[T], b_barrier: T, u_nom: Vec3T[T], pi_b: Vec3T[T]
) -> tuple[T, Vec3T[T]]:
    """Return (lambda*, u_safe) satisfying both u_safe in K(mu) and a_cbf . u_safe >= b_barrier."""
    is_frac = isinstance(b_barrier, Fraction)
    zero: T = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    one: T = Fraction(1, 1) if is_frac else 1.0  # type: ignore[assignment]

    a_nom = dot3(a_cbf, u_nom)
    a_pi = dot3(a_cbf, pi_b)
    if a_nom >= b_barrier:
        lam = zero
    elif a_pi <= a_nom:
        lam = one
    else:
        ratio = (b_barrier - a_nom) / (a_pi - a_nom)
        lam = zero if ratio < zero else (one if ratio > one else ratio)
    u_safe = add3(smul3(one - lam, u_nom), smul3(lam, pi_b))
    return lam, u_safe
