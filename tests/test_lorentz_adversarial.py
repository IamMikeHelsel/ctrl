"""Adversarial Property-Based Tests for Centroidal Lorentz-Cone Backup CBF.

Written by challenger_m2_1 to verify:
1. Absence of counterexamples to cone convexity under extreme aspect ratios,
   orthogonal boundary vectors, and opposite boundary vectors.
2. Boundary chord interiority and grazing cases (u_z = 0, apex).
3. Equal authority cases (a . pi_b == a . u_nom).
4. Strict [0, 1] bounds on lambda*(x) whenever a valid backup exists.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.verify_lorentz_cbf import (  # noqa: E402
    Vec3Q,
    compute_lambda_star,
    verify_conic_convexity_decomposition,
)


@pytest.mark.parametrize("mu", [
    Fraction(1, 10**18),
    Fraction(1, 10**6),
    Fraction(1, 100),
    Fraction(1, 2),
    Fraction(1),
    Fraction(100),
    Fraction(10**6),
    Fraction(10**18),
    Fraction(0),
])
def test_convexity_under_extreme_aspect_ratios(mu):
    """Convex combinations remain in Lorentz cone under extreme aspect ratios."""
    z1 = Fraction(1, 100)
    z2 = Fraction(100)
    # Opposite boundary vectors
    u1 = Vec3Q(mu * z1, Fraction(0), z1)
    u2 = Vec3Q(-mu * z2, Fraction(0), z2)
    assert u1.in_lorentz_cone(mu)
    assert u2.in_lorentz_cone(mu)

    for lam in [Fraction(0), Fraction(1, 10), Fraction(1, 2), Fraction(9, 10), Fraction(1)]:
        w = (Fraction(1) - lam) * u1 + lam * u2
        assert w.in_lorentz_cone(mu)
        assert verify_conic_convexity_decomposition(u1, u2, mu, lam)


def test_orthogonal_boundary_vectors_convexity():
    """Orthogonal boundary vectors combination is always in cone interior for 0 < lam < 1."""
    mu = Fraction(6, 10)
    z = Fraction(10)
    u1 = Vec3Q(mu * z, Fraction(0), z)
    u2 = Vec3Q(Fraction(0), mu * z, z)

    assert u1.lorentz_margin(mu) == 0
    assert u2.lorentz_margin(mu) == 0

    for lam in [Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)]:
        w = (Fraction(1) - lam) * u1 + lam * u2
        assert w.in_lorentz_cone(mu)
        # Must be strictly in interior
        assert w.lorentz_margin(mu) > 0


def test_grazing_uz_zero():
    """Only origin has u_z = 0 in the Lorentz cone."""
    mu = Fraction(6, 10)
    origin = Vec3Q.from_values(0, 0, 0)
    assert origin.in_lorentz_cone(mu)

    # Any non-zero vector with u_z = 0 is outside
    assert not Vec3Q.from_values(Fraction(1, 1000), 0, 0).in_lorentz_cone(mu)
    assert not Vec3Q.from_values(0, Fraction(1, 1000), 0).in_lorentz_cone(mu)

    # Combination with origin is positive scaling
    u = Vec3Q.from_values(mu * 2, 0, 2)
    for lam in [Fraction(0), Fraction(1, 3), Fraction(1)]:
        w = (Fraction(1) - lam) * origin + lam * u
        assert w.in_lorentz_cone(mu)


def test_equal_authority_grazing():
    """When a(x) . pi_b == a(x) . u_nom:

    - If nominal is safe (b <= a_nom), lambda* = 0 and control is safe.
    - If nominal is unsafe (b > a_nom), backup lacks authority, raising ValueError.
    """
    a_nom = Fraction(3)
    a_pi = Fraction(3)

    # Safe nominal: b <= 3
    assert compute_lambda_star(Fraction(2), a_nom, a_pi) == Fraction(0)
    assert compute_lambda_star(Fraction(3), a_nom, a_pi) == Fraction(0)

    # Unsafe nominal: b > 3 -> raises ValueError
    with pytest.raises(ValueError, match="Backup policy lacks authority"):
        compute_lambda_star(Fraction(4), a_nom, a_pi)


@pytest.mark.parametrize("b, a_nom, a_pi", [
    (Fraction(0), Fraction(0), Fraction(10)),
    (Fraction(10), Fraction(0), Fraction(10)),
    (Fraction(5), Fraction(0), Fraction(10)),
    (Fraction(2), Fraction(5), Fraction(10)),   # nominal safe
    (-Fraction(2), -Fraction(8), -Fraction(1)), # negative regime
    (Fraction(1, 10**6), Fraction(0), Fraction(1)),
    (Fraction(10**6 - 1), Fraction(0), Fraction(10**6)),
])
def test_lambda_star_bounded_in_unit_interval(b, a_nom, a_pi):
    """When valid backup exists (b <= a_pi), lambda* is strictly in [0, 1]."""
    lam = compute_lambda_star(b, a_nom, a_pi)
    assert Fraction(0) <= lam <= Fraction(1)
    if b <= a_nom:
        assert lam == Fraction(0)
    else:
        assert lam == (b - a_nom) / (a_pi - a_nom)
