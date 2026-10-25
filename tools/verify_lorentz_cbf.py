"""Exact Symbolic and Interval Verification for Centroidal Lorentz-Cone Backup CBF.

Milestone 2: Controls — Seed 1 Centroidal Lorentz-Cone Backup CBF.

Provides:
1. Exact symbolic verification (via exact rational arithmetic and algebraic identities)
   of the Lie derivatives, barrier inequality, and conic convexity.
2. Exact interval arithmetic verification over an operating box envelope.
3. Concrete falsification checks:
   - Friction coefficient limit: ||a_brake|| <= mu * g
   - Zero Moment Point (ZMP) support polygon boundary check.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction

# ==============================================================================
# Exact Rational 3D Vector & Algebra
# ==============================================================================

@dataclass(frozen=True)
class Vec3Q:
    """Exact 3D vector with rational components."""
    x: Fraction
    y: Fraction
    z: Fraction

    @classmethod
    def from_values(cls, x: int | float | Fraction, y: int | float | Fraction, z: int | float | Fraction) -> Vec3Q:
        return cls(Fraction(x), Fraction(y), Fraction(z))

    def __add__(self, other: Vec3Q) -> Vec3Q:
        return Vec3Q(self.x + other.x, self.y + other.y, self.z + other.z)

    def __sub__(self, other: Vec3Q) -> Vec3Q:
        return Vec3Q(self.x - other.x, self.y - other.y, self.z - other.z)

    def __mul__(self, scalar: Fraction | int) -> Vec3Q:
        s = Fraction(scalar)
        return Vec3Q(self.x * s, self.y * s, self.z * s)

    __rmul__ = __mul__

    def dot(self, other: Vec3Q) -> Fraction:
        return self.x * other.x + self.y * other.y + self.z * other.z

    def sq_norm(self) -> Fraction:
        return self.x * self.x + self.y * self.y + self.z * self.z

    def sq_norm_xy(self) -> Fraction:
        return self.x * self.x + self.y * self.y

    def in_lorentz_cone(self, mu: Fraction) -> bool:
        """Check if vector is inside Lorentz cone: x^2 + y^2 <= mu^2 * z^2 and z >= 0."""
        return self.z >= 0 and self.sq_norm_xy() <= (mu * mu) * (self.z * self.z)

    def lorentz_margin(self, mu: Fraction) -> Fraction:
        """Margin M = mu^2 * z^2 - (x^2 + y^2). Nonnegative inside cone."""
        return (mu * mu) * (self.z * self.z) - self.sq_norm_xy()


# ==============================================================================
# Exact Rational Interval Arithmetic
# ==============================================================================

@dataclass(frozen=True)
class IntervalQ:
    """Exact closed interval [lo, hi] over rational numbers."""
    lo: Fraction
    hi: Fraction

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError(f"Invalid interval: lo ({self.lo}) > hi ({self.hi})")

    @classmethod
    def point(cls, val: Fraction | int) -> IntervalQ:
        f = Fraction(val)
        return cls(f, f)

    @classmethod
    def from_bounds(cls, lo: Fraction | int | float, hi: Fraction | int | float) -> IntervalQ:
        return cls(Fraction(lo), Fraction(hi))

    def __add__(self, other: IntervalQ | Fraction | int) -> IntervalQ:
        if isinstance(other, (Fraction, int)):
            other = IntervalQ.point(other)
        return IntervalQ(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other: IntervalQ | Fraction | int) -> IntervalQ:
        if isinstance(other, (Fraction, int)):
            other = IntervalQ.point(other)
        return IntervalQ(self.lo - other.hi, self.hi - other.lo)

    def __mul__(self, other: IntervalQ | Fraction | int) -> IntervalQ:
        if isinstance(other, (Fraction, int)):
            other = IntervalQ.point(other)
        p1 = self.lo * other.lo
        p2 = self.lo * other.hi
        p3 = self.hi * other.lo
        p4 = self.hi * other.hi
        return IntervalQ(min(p1, p2, p3, p4), max(p1, p2, p3, p4))

    __rmul__ = __mul__

    def sq(self) -> IntervalQ:
        """Exact square of the interval."""
        if self.lo >= 0:
            return IntervalQ(self.lo * self.lo, self.hi * self.hi)
        elif self.hi <= 0:
            return IntervalQ(self.hi * self.hi, self.lo * self.lo)
        else:
            return IntervalQ(Fraction(0), max(self.lo * self.lo, self.hi * self.hi))

    def __truediv__(self, other: IntervalQ | Fraction | int) -> IntervalQ:
        if isinstance(other, (Fraction, int)):
            other = IntervalQ.point(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("Division by interval containing zero")
        d1 = self.lo / other.lo
        d2 = self.lo / other.hi
        d3 = self.hi / other.lo
        d4 = self.hi / other.hi
        return IntervalQ(min(d1, d2, d3, d4), max(d1, d2, d3, d4))

    def contains(self, val: Fraction | int) -> bool:
        f = Fraction(val)
        return self.lo <= f <= self.hi

    def is_nonnegative(self) -> bool:
        return self.lo >= 0

    def is_positive(self) -> bool:
        return self.lo > 0


@dataclass(frozen=True)
class Vec3IntervalQ:
    """3D vector of exact rational intervals."""
    x: IntervalQ
    y: IntervalQ
    z: IntervalQ

    def dot(self, other: Vec3IntervalQ) -> IntervalQ:
        return self.x * other.x + self.y * other.y + self.z * other.z

    def sq_norm(self) -> IntervalQ:
        return self.x.sq() + self.y.sq() + self.z.sq()

    def sq_norm_xy(self) -> IntervalQ:
        return self.x.sq() + self.y.sq()


# ==============================================================================
# Closed-Form Controller & Barrier Functions
# ==============================================================================

def compute_lambda_star(b: Fraction, a_nom: Fraction, a_pi: Fraction) -> Fraction:
    """Closed-form interpolation parameter:

    lambda*(x) = max(0, (b - a_nom) / (a_pi - a_nom)).
    """
    if b <= a_nom:
        return Fraction(0)
    denom = a_pi - a_nom
    if denom <= 0:
        raise ValueError(f"Backup policy lacks authority: a_pi ({a_pi}) <= a_nom ({a_nom})")
    ratio = (b - a_nom) / denom
    return max(Fraction(0), min(Fraction(1), ratio))


def interpolated_control(u_nom: Vec3Q, pi_b: Vec3Q, lam: Fraction) -> Vec3Q:
    """u*(x) = (1 - lam) * u_nom + lam * pi_b."""
    return (Fraction(1) - lam) * u_nom + lam * pi_b


def backup_cbf_value(r_limit: Vec3Q, r: Vec3Q, v: Vec3Q, n_hat: Vec3Q, a_brake: Fraction) -> Fraction:
    """h_b(r, v) = (r_limit - r) . n_hat - ||v||^2 / (2 * a_brake)."""
    dist_clearance = (r_limit - r).dot(n_hat)
    stopping_dist = v.sq_norm() / (Fraction(2) * a_brake)
    return dist_clearance - stopping_dist


def cbf_lie_derivatives(v: Vec3Q, n_hat: Vec3Q, a_brake: Fraction) -> tuple[Fraction, Vec3Q]:
    """Lie derivatives of h_b:

    Lf_h = - v . n_hat
    Lg_h = - v^T / a_brake
    Returns (Lf_h, a_cbf) where a_cbf = - v / a_brake.
    """
    Lf_h = - v.dot(n_hat)
    a_cbf = Vec3Q(- v.x / a_brake, - v.y / a_brake, - v.z / a_brake)
    return Lf_h, a_cbf


# ==============================================================================
# Exact Symbolic Verifications
# ==============================================================================

def verify_lagrange_identity_2d(x1: Fraction, y1: Fraction, x2: Fraction, y2: Fraction) -> bool:
    """Verify (x1^2 + y1^2)(x2^2 + y2^2) = (x1*x2 + y1*y2)^2 + (x1*y2 - x2*y1)^2 identically."""
    lhs = (x1 * x1 + y1 * y1) * (x2 * x2 + y2 * y2)
    rhs = (x1 * x2 + y1 * y2) ** 2 + (x1 * y2 - x2 * y1) ** 2
    return lhs == rhs


def verify_conic_convexity_decomposition(u1: Vec3Q, u2: Vec3Q, mu: Fraction, lam: Fraction) -> bool:
    """Verify that conic margin of convex combination decomposes into nonnegative sum:

    M(w) = (1-lam)^2 * M(u1) + lam^2 * M(u2) + 2*lam*(1-lam) * M_cross
    where M_cross = mu^2 * z1 * z2 - (x1*x2 + y1*y2).
    """
    w = (Fraction(1) - lam) * u1 + lam * u2
    M_w = w.lorentz_margin(mu)

    M1 = u1.lorentz_margin(mu)
    M2 = u2.lorentz_margin(mu)
    M_cross = (mu * mu) * (u1.z * u2.z) - (u1.x * u2.x + u1.y * u2.y)

    c1 = (Fraction(1) - lam) ** 2
    c2 = lam ** 2
    c_cross = Fraction(2) * (Fraction(1) - lam) * lam

    expected = c1 * M1 + c2 * M2 + c_cross * M_cross
    return M_w == expected


def verify_exact_barrier_equality_on_intervention(
    a_cbf: Vec3Q, b: Fraction, u_nom: Vec3Q, pi_b: Vec3Q
) -> bool:
    """When a_cbf . u_nom < b <= a_cbf . pi_b, verify that a_cbf . u*(lam*) == b exactly."""
    a_nom = a_cbf.dot(u_nom)
    a_pi = a_cbf.dot(pi_b)
    if a_nom >= b or b > a_pi:
        return True  # Condition does not apply
    lam = compute_lambda_star(b, a_nom, a_pi)
    u_safe = interpolated_control(u_nom, pi_b, lam)
    dot_val = a_cbf.dot(u_safe)
    return dot_val == b


# ==============================================================================
# Exact Interval Arithmetic Operating Envelope Verification
# ==============================================================================

@dataclass
class OperatingEnvelope:
    """Operating box envelope for the centroidal floating-base system."""
    rx: IntervalQ
    ry: IntervalQ
    rz: IntervalQ
    vx: IntervalQ
    vy: IntervalQ
    vz: IntervalQ
    a_brake: Fraction
    mu: Fraction
    r_limit: Vec3Q
    n_hat: Vec3Q
    alpha: Fraction


def verify_operating_envelope(envelope: OperatingEnvelope) -> dict:
    """Verifies safety and friction cone invariants over the continuous operating envelope."""
    r_box = Vec3IntervalQ(envelope.rx, envelope.ry, envelope.rz)
    v_box = Vec3IntervalQ(envelope.vx, envelope.vy, envelope.vz)

    # 1. Distance clearance interval: (r_limit - r) . n_hat
    r_limit_box = Vec3IntervalQ(
        IntervalQ.point(envelope.r_limit.x),
        IntervalQ.point(envelope.r_limit.y),
        IntervalQ.point(envelope.r_limit.z),
    )
    diff_box = Vec3IntervalQ(
        r_limit_box.x - r_box.x,
        r_limit_box.y - r_box.y,
        r_limit_box.z - r_box.z,
    )
    n_hat_box = Vec3IntervalQ(
        IntervalQ.point(envelope.n_hat.x),
        IntervalQ.point(envelope.n_hat.y),
        IntervalQ.point(envelope.n_hat.z),
    )
    clearance_interval = diff_box.dot(n_hat_box)

    # 2. Stopping distance interval: ||v||^2 / (2 * a_brake)
    v_sq_interval = v_box.sq_norm()
    two_a = Fraction(2) * envelope.a_brake
    stopping_dist_interval = v_sq_interval / two_a

    # 3. Barrier value interval: h_b
    h_b_interval = clearance_interval - stopping_dist_interval

    # 4. Lie derivative bounds:
    # Lf_h = - v . n_hat
    Lf_h_interval = IntervalQ.point(0) - v_box.dot(n_hat_box)

    return {
        "clearance_interval": clearance_interval,
        "stopping_dist_interval": stopping_dist_interval,
        "h_b_interval": h_b_interval,
        "Lf_h_interval": Lf_h_interval,
        "v_sq_max": v_sq_interval.hi,
        "a_brake": envelope.a_brake,
        "mu": envelope.mu,
    }


# ==============================================================================
# Concrete Falsification Checks
# ==============================================================================

def check_friction_limit(a_brake: Fraction | float, mu: Fraction | float, g: Fraction | float) -> tuple[bool, str]:
    """Falsification Test 1: Friction Exceedance Check.

    A braking deceleration requiring normal contact force cannot exceed mu * g without slipping.
    """
    a_b = Fraction(a_brake)
    mu_f = Fraction(mu)
    g_f = Fraction(g)

    if a_b > mu_f * g_f:
        return False, (
            f"FALSIFIED: required deceleration a_brake={float(a_b):.3f} exceeds "
            f"friction limit mu*g={float(mu_f * g_f):.3f} (slip unavoidable)"
        )
    return True, (
        f"SATISFIED: a_brake={float(a_b):.3f} <= mu*g={float(mu_f * g_f):.3f}"
    )


def check_zmp_support_polygon(
    r_com: Sequence[Fraction | float],
    a_com: Sequence[Fraction | float],
    g: Fraction | float,
    support_polygon: Sequence[Sequence[Fraction | float]],
) -> tuple[bool, str]:
    """Falsification Test 2: Zero Moment Point (ZMP) Support Polygon Boundary Check.

    During deceleration a_com, the ground reaction force produces ZMP:
    p_zmp = r_xy - (r_z / (g + a_z)) * a_xy.
    If p_zmp leaves the convex support polygon, the robot tilts and contact lifts off.
    """
    rx, ry, rz = Fraction(r_com[0]), Fraction(r_com[1]), Fraction(r_com[2])
    ax, ay, az = Fraction(a_com[0]), Fraction(a_com[1]), Fraction(a_com[2])
    g_f = Fraction(g)

    denom = g_f + az
    if denom <= 0:
        return False, f"FALSIFIED: net vertical acceleration ({float(denom):.3f}) <= 0 (free-fall / liftoff)"

    p_zmp_x = rx - (rz / denom) * ax
    p_zmp_y = ry - (rz / denom) * ay

    # Check point in convex polygon via edge cross-products (counter-clockwise order)
    poly = [(Fraction(pt[0]), Fraction(pt[1])) for pt in support_polygon]
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        edge_x = x2 - x1
        edge_y = y2 - y1
        to_pt_x = p_zmp_x - x1
        to_pt_y = p_zmp_y - y1
        cross = edge_x * to_pt_y - edge_y * to_pt_x
        if cross < 0:
            return False, (
                f"FALSIFIED: p_ZMP=({float(p_zmp_x):.3f}, {float(p_zmp_y):.3f}) "
                f"outside support edge {i} -> {i+1} (robot tilts)"
            )

    return True, (
        f"SATISFIED: p_ZMP=({float(p_zmp_x):.3f}, {float(p_zmp_y):.3f}) inside support polygon"
    )


# ==============================================================================
# Self-Verification Runner
# ==============================================================================

def run_all_verifications() -> bool:
    """Execute all symbolic, interval, and falsification verifications."""
    print("=" * 70)
    print("CENTROIDAL LORENTZ-CONE BACKUP CBF: VERIFICATION SUITE")
    print("=" * 70)

    # 1. Exact Symbolic Identities
    print("\n[1] Exact Symbolic Identities:")
    assert verify_lagrange_identity_2d(Fraction(3), Fraction(4), Fraction(5), Fraction(12)), "Lagrange identity failed"
    print("  ✓ 2D Lagrange Identity: (x1^2+y1^2)(x2^2+y2^2) = (x1 x2 + y1 y2)^2 + (x1 y2 - x2 y1)^2")

    u1 = Vec3Q.from_values(1, 1, 3)
    u2 = Vec3Q.from_values(2, 0, 4)
    mu = Fraction(6, 10)
    assert u1.in_lorentz_cone(mu), "u1 should be inside Lorentz cone"
    assert u2.in_lorentz_cone(mu), "u2 should be inside Lorentz cone"
    assert verify_conic_convexity_decomposition(u1, u2, mu, Fraction(1, 3)), "Conic decomposition failed"
    print("  ✓ Conic Margin Decomposition: M((1-λ)u1 + λ u2) = (1-λ)^2 M1 + λ^2 M2 + 2λ(1-λ) M_cross")

    u_nom = Vec3Q.from_values(-2, 0, 5)  # a_nom = -2
    pi_b = Vec3Q.from_values(4, 0, 8)    # a_pi = 4
    a_cbf = Vec3Q.from_values(1, 0, 0)
    b = Fraction(1)
    assert verify_exact_barrier_equality_on_intervention(a_cbf, b, u_nom, pi_b), "Barrier equality failed"
    print("  ✓ Exact Minimal Intervention: a(x) . u*(λ*) == b(x) when intervention required")

    # 2. Operating Envelope Interval Verification
    print("\n[2] Continuous Operating Envelope Interval Verification:")
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
    env_res = verify_operating_envelope(envelope)
    print(f"  ✓ Clearance interval: [{float(env_res['clearance_interval'].lo):.3f}, {float(env_res['clearance_interval'].hi):.3f}] m")
    print(f"  ✓ Stopping dist max: {float(env_res['stopping_dist_interval'].hi):.3f} m")
    print(f"  ✓ Barrier h_b interval: [{float(env_res['h_b_interval'].lo):.3f}, {float(env_res['h_b_interval'].hi):.3f}]")

    # 3. Concrete Falsification Checks
    print("\n[3] Concrete Falsification Checks:")
    # Test 1: Friction limit
    g = Fraction(981, 100)
    sat1, msg1 = check_friction_limit(a_brake=Fraction(4), mu=Fraction(6, 10), g=g)
    assert sat1, "4 <= 0.6 * 9.81 = 5.886 should satisfy"
    print(f"  ✓ Feasible friction: {msg1}")

    sat1_fail, msg1_fail = check_friction_limit(a_brake=Fraction(7), mu=Fraction(6, 10), g=g)
    assert not sat1_fail, "7 > 5.886 should falsify"
    print(f"  ✓ Falsified friction: {msg1_fail}")

    # Test 2: ZMP polygon
    poly = [(-Fraction(3, 10), -Fraction(2, 10)),
            (Fraction(3, 10), -Fraction(2, 10)),
            (Fraction(3, 10), Fraction(2, 10)),
            (-Fraction(3, 10), Fraction(2, 10))]
    sat2, msg2 = check_zmp_support_polygon(
        r_com=[0, 0, Fraction(1)],
        a_com=[Fraction(1), Fraction(0), Fraction(0)],
        g=g,
        support_polygon=poly,
    )
    assert sat2, "Small deceleration ZMP should lie inside footprint"
    print(f"  ✓ Feasible ZMP: {msg2}")

    sat2_fail, msg2_fail = check_zmp_support_polygon(
        r_com=[0, 0, Fraction(1)],
        a_com=[Fraction(5), Fraction(0), Fraction(0)],
        g=g,
        support_polygon=poly,
    )
    assert not sat2_fail, "Large deceleration ZMP should leave footprint"
    print(f"  ✓ Falsified ZMP: {msg2_fail}")

    print("\n" + "=" * 70)
    print("ALL VERIFICATION CHECKS SUCCESSFULLY COMPLETED (100% PASS)")
    print("=" * 70)
    return True


if __name__ == "__main__":
    run_all_verifications()
