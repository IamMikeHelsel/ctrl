from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import pytest

# Ensure repository root is on sys.path for running pytest directly
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.verify_lorentz_cbf import (  # noqa: E402
    IntervalQ,
    OperatingEnvelope,
    Vec3Q,
    backup_cbf_value,
    cbf_lie_derivatives,
    check_friction_limit,
    check_zmp_support_polygon,
    compute_lambda_star,
    interpolated_control,
    verify_conic_convexity_decomposition,
    verify_exact_barrier_equality_on_intervention,
    verify_lagrange_identity_2d,
    verify_operating_envelope,
)

# ==============================================================================
# 1. Exact Symbolic & Algebraic Properties
# ==============================================================================

@pytest.mark.parametrize("x1, y1, x2, y2", [
    (1, 2, 3, 4),
    (0, 0, 5, 7),
    (-3, 4, 12, -5),
    (Fraction(1, 3), Fraction(2, 5), Fraction(7, 11), Fraction(4, 9)),
    (-Fraction(8, 7), Fraction(15, 7), Fraction(20, 3), -Fraction(5, 2)),
])
def test_lagrange_identity_2d_across_scalars(x1, y1, x2, y2):
    """(x1^2 + y1^2)(x2^2 + y2^2) = (x1*x2 + y1*y2)^2 + (x1*y2 - x2*y1)^2 identically."""
    assert verify_lagrange_identity_2d(Fraction(x1), Fraction(y1), Fraction(x2), Fraction(y2))


def test_cauchy_schwarz_2d_residual_nonnegative():
    """Lagrange remainder term (x1*y2 - x2*y1)^2 is non-negative, proving Cauchy-Schwarz."""
    x1, y1 = Fraction(3, 2), Fraction(-5, 4)
    x2, y2 = Fraction(7, 3), Fraction(11, 6)
    remainder = (x1 * y2 - x2 * y1) ** 2
    assert remainder >= 0
    lhs = (x1 * x1 + y1 * y1) * (x2 * x2 + y2 * y2)
    rhs = (x1 * x2 + y1 * y2) ** 2
    assert lhs >= rhs


@pytest.mark.parametrize("lam", [
    Fraction(0),
    Fraction(1, 10),
    Fraction(1, 4),
    Fraction(1, 2),
    Fraction(3, 4),
    Fraction(9, 10),
    Fraction(1),
])
def test_conic_margin_decomposition(lam):
    """M((1-lam)u1 + lam*u2) = (1-lam)^2 M1 + lam^2 M2 + 2*lam*(1-lam) M_cross."""
    mu = Fraction(6, 10)
    u1 = Vec3Q.from_values(1, 1, 4)
    u2 = Vec3Q.from_values(2, -1, 5)
    assert u1.in_lorentz_cone(mu)
    assert u2.in_lorentz_cone(mu)
    assert verify_conic_convexity_decomposition(u1, u2, mu, lam)


def test_exact_barrier_equality_on_intervention():
    """When a(x) . u_nom < b <= a(x) . pi_b, a(x) . u*(lam*) == b exactly."""
    a_cbf = Vec3Q.from_values(2, -1, 0)
    u_nom = Vec3Q.from_values(0, 2, 5)   # a_nom = -2
    pi_b = Vec3Q.from_values(3, 0, 8)    # a_pi = 6
    b = Fraction(2)                       # a_nom < b <= a_pi
    assert verify_exact_barrier_equality_on_intervention(a_cbf, b, u_nom, pi_b)

    # Check exact value
    lam = compute_lambda_star(b, a_cbf.dot(u_nom), a_cbf.dot(pi_b))
    assert lam == Fraction(2 - (-2), 6 - (-2))  # 4/8 = 1/2
    u_safe = interpolated_control(u_nom, pi_b, lam)
    assert a_cbf.dot(u_safe) == b


def test_barrier_strict_satisfaction_when_nominal_safe():
    """When a(x) . u_nom >= b, lambda* = 0, u* = u_nom, barrier is satisfied."""
    a_cbf = Vec3Q.from_values(1, 0, 0)
    u_nom = Vec3Q.from_values(3, 0, 6)   # a_nom = 3
    pi_b = Vec3Q.from_values(5, 0, 10)   # a_pi = 5
    b = Fraction(2)                      # b <= a_nom
    lam = compute_lambda_star(b, a_cbf.dot(u_nom), a_cbf.dot(pi_b))
    assert lam == Fraction(0)
    u_safe = interpolated_control(u_nom, pi_b, lam)
    assert u_safe == u_nom
    assert a_cbf.dot(u_safe) >= b


# ==============================================================================
# 2. Convex Interpolation Validity
# ==============================================================================

@pytest.mark.parametrize("b, a_nom, a_pi, expected_lam", [
    (Fraction(1), Fraction(0), Fraction(2), Fraction(1, 2)),
    (Fraction(0), Fraction(0), Fraction(5), Fraction(0)),
    (Fraction(5), Fraction(0), Fraction(5), Fraction(1)),
    (-Fraction(2), -Fraction(4), Fraction(4), Fraction(2, 8)),
    (Fraction(3), Fraction(4), Fraction(8), Fraction(0)),  # Safe nominal
])
def test_lambda_star_values(b, a_nom, a_pi, expected_lam):
    """compute_lambda_star produces exact rational values inside [0, 1]."""
    lam = compute_lambda_star(b, a_nom, a_pi)
    assert lam == expected_lam
    assert Fraction(0) <= lam <= Fraction(1)


def test_lambda_star_raises_on_invalid_authority():
    """compute_lambda_star raises ValueError when intervention is needed (b > a_nom) but backup lacks authority (a_pi <= a_nom)."""
    with pytest.raises(ValueError, match="Backup policy lacks authority"):
        compute_lambda_star(Fraction(5), Fraction(3), Fraction(3))
    with pytest.raises(ValueError, match="Backup policy lacks authority"):
        compute_lambda_star(Fraction(5), Fraction(4), Fraction(2))


def test_interpolated_control_stays_in_cone():
    """Convex combinations of cone vectors remain strictly inside the cone."""
    mu = Fraction(7, 10)
    u_nom = Vec3Q.from_values(1, 1, 3)
    pi_b = Vec3Q.from_values(0, 2, 4)
    assert u_nom.in_lorentz_cone(mu)
    assert pi_b.in_lorentz_cone(mu)

    for i in range(11):
        lam = Fraction(i, 10)
        u_interp = interpolated_control(u_nom, pi_b, lam)
        assert u_interp.in_lorentz_cone(mu)
        assert u_interp.lorentz_margin(mu) >= 0


# ==============================================================================
# 3. Friction Cone Admissibility & Projections
# ==============================================================================

def test_lorentz_cone_membership():
    """Verify interior, boundary, exterior, and negative normal force."""
    mu = Fraction(1, 2)  # mu^2 = 1/4
    # Interior: x^2 + y^2 < (1/4) * z^2
    assert Vec3Q.from_values(0, 0, 1).in_lorentz_cone(mu)
    assert Vec3Q.from_values(1, 0, 3).in_lorentz_cone(mu)  # 1 <= 9/4 = 2.25

    # Boundary: x^2 + y^2 == (1/4) * z^2
    assert Vec3Q.from_values(1, 0, 2).in_lorentz_cone(mu)  # 1 == 4/4 = 1

    # Exterior: x^2 + y^2 > (1/4) * z^2
    assert not Vec3Q.from_values(2, 0, 2).in_lorentz_cone(mu)  # 4 > 1

    # Negative normal force (z < 0): must NOT be in friction cone
    assert not Vec3Q.from_values(0, 0, -1).in_lorentz_cone(mu)
    assert not Vec3Q.from_values(1, 0, -3).in_lorentz_cone(mu)


def test_lorentz_cone_positive_scaling():
    """If u in K(mu), then c * u in K(mu) for all c >= 0."""
    mu = Fraction(6, 10)
    u = Vec3Q.from_values(1, 2, 5)
    assert u.in_lorentz_cone(mu)

    for c in [0, 1, 2, Fraction(1, 5), Fraction(17, 3)]:
        cu = Fraction(c) * u
        assert cu.in_lorentz_cone(mu)


# ==============================================================================
# 4. Backup CBF Physics & Lie Derivatives
# ==============================================================================

def test_backup_cbf_value():
    """Verify scalar stopping-distance backup barrier computation."""
    r_limit = Vec3Q.from_values(5, 0, 0)
    r = Vec3Q.from_values(2, 0, 0)
    v = Vec3Q.from_values(3, 0, 0)
    n_hat = Vec3Q.from_values(1, 0, 0)
    a_brake = Fraction(3)

    # dist_clearance = (5 - 2) * 1 = 3
    # stopping_dist = 9 / (2 * 3) = 1.5
    # h_b = 3 - 1.5 = 1.5
    h_b = backup_cbf_value(r_limit, r, v, n_hat, a_brake)
    assert h_b == Fraction(3, 2)


def test_backup_cbf_lie_derivatives():
    """Verify Lf_h = - v . n_hat and Lg_h = - v^T / a_brake."""
    v = Vec3Q.from_values(2, 4, 1)
    n_hat = Vec3Q.from_values(0, 1, 0)
    a_brake = Fraction(2)

    Lf_h, a_cbf = cbf_lie_derivatives(v, n_hat, a_brake)
    assert Lf_h == - Fraction(4)
    assert a_cbf == Vec3Q.from_values(-1, -2, -Fraction(1, 2))


def test_backup_cbf_safe_at_rest():
    """h_b(r, 0) >= 0 implies position clearance (r_limit - r) . n_hat >= 0."""
    r_limit = Vec3Q.from_values(4, 0, 0)
    r = Vec3Q.from_values(1, 0, 0)
    v_zero = Vec3Q.from_values(0, 0, 0)
    n_hat = Vec3Q.from_values(1, 0, 0)
    a_brake = Fraction(3)

    h_b = backup_cbf_value(r_limit, r, v_zero, n_hat, a_brake)
    assert h_b == Fraction(3) >= 0
    assert (r_limit - r).dot(n_hat) >= 0


# ==============================================================================
# 5. Exact Rational Interval Arithmetic & Operating Envelope
# ==============================================================================

def test_interval_arithmetic_basic_operations():
    """Test IntervalQ arithmetic accuracy."""
    i1 = IntervalQ.from_bounds(-1, 2)
    i2 = IntervalQ.from_bounds(3, 5)

    # Addition
    i_add = i1 + i2
    assert i_add.lo == Fraction(2) and i_add.hi == Fraction(7)

    # Subtraction
    i_sub = i1 - i2
    assert i_sub.lo == Fraction(-6) and i_sub.hi == Fraction(-1)

    # Multiplication
    i_mul = i1 * i2
    assert i_mul.lo == Fraction(-5) and i_mul.hi == Fraction(10)

    # Square containing zero
    i_sq = i1.sq()
    assert i_sq.lo == Fraction(0) and i_sq.hi == Fraction(4)

    # Division
    i_div = i2 / IntervalQ.from_bounds(1, 2)
    assert i_div.lo == Fraction(3, 2) and i_div.hi == Fraction(5)


def test_operating_envelope_verification():
    """Verify operating envelope returns certified positive clearance and bounded stopping distance."""
    envelope = OperatingEnvelope(
        rx=IntervalQ.from_bounds(-1, 1),
        ry=IntervalQ.from_bounds(-1, 1),
        rz=IntervalQ.from_bounds(Fraction(8, 10), Fraction(12, 10)),
        vx=IntervalQ.from_bounds(-1, 1),
        vy=IntervalQ.from_bounds(-1, 1),
        vz=IntervalQ.from_bounds(Fraction(-2, 10), Fraction(2, 10)),
        a_brake=Fraction(3),
        mu=Fraction(6, 10),
        r_limit=Vec3Q.from_values(3, 0, 0),
        n_hat=Vec3Q.from_values(1, 0, 0),
        alpha=Fraction(1),
    )
    res = verify_operating_envelope(envelope)
    assert res["clearance_interval"].lo >= Fraction(2)
    assert res["stopping_dist_interval"].hi <= Fraction(1)
    assert res["h_b_interval"].lo > Fraction(0)


# ==============================================================================
# 6. Concrete Falsification Checks
# ==============================================================================

def test_friction_limit_falsification():
    """check_friction_limit accurately checks ||a_brake|| <= mu * g."""
    g = Fraction(981, 100)  # 9.81
    mu = Fraction(6, 10)    # 0.6 -> mu * g = 5.886

    # Feasible: a_brake = 4.0 <= 5.886
    sat, msg = check_friction_limit(Fraction(4), mu, g)
    assert sat
    assert "SATISFIED" in msg

    # Boundary: a_brake = mu * g
    sat_b, _ = check_friction_limit(mu * g, mu, g)
    assert sat_b

    # Falsified: a_brake = 6.0 > 5.886
    sat_f, msg_f = check_friction_limit(Fraction(6), mu, g)
    assert not sat_f
    assert "FALSIFIED" in msg_f


def test_zmp_support_polygon_falsification():
    """check_zmp_support_polygon detects when deceleration forces ZMP out of support polygon."""
    g = Fraction(981, 100)
    support_poly = [
        (-Fraction(2, 10), -Fraction(2, 10)),
        (Fraction(2, 10), -Fraction(2, 10)),
        (Fraction(2, 10), Fraction(2, 10)),
        (-Fraction(2, 10), Fraction(2, 10)),
    ]

    # Mild deceleration: p_zmp inside
    sat, msg = check_zmp_support_polygon(
        r_com=[0, 0, 1],
        a_com=[Fraction(1), 0, 0],
        g=g,
        support_polygon=support_poly,
    )
    assert sat
    assert "SATISFIED" in msg

    # Severe deceleration: a_x = 4 -> p_zmp_x = - (1 / 9.81) * 4 = -0.407 < -0.2 (leaves box)
    sat_f, msg_f = check_zmp_support_polygon(
        r_com=[0, 0, 1],
        a_com=[Fraction(4), 0, 0],
        g=g,
        support_polygon=support_poly,
    )
    assert not sat_f
    assert "FALSIFIED" in msg_f


def test_zmp_liftoff_falsification():
    """check_zmp_support_polygon detects free-fall/liftoff when g + a_z <= 0."""
    g = Fraction(981, 100)
    support_poly = [(-1, -1), (1, -1), (1, 1), (-1, 1)]

    sat, msg = check_zmp_support_polygon(
        r_com=[0, 0, 1],
        a_com=[0, 0, -Fraction(10)],  # g + a_z = 9.81 - 10 = -0.19 < 0
        g=g,
        support_polygon=support_poly,
    )
    assert not sat
    assert "free-fall / liftoff" in msg
