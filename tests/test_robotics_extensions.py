from __future__ import annotations

from fractions import Fraction


def cross3(
    u: tuple[Fraction, Fraction, Fraction], v: tuple[Fraction, Fraction, Fraction]
) -> tuple[Fraction, Fraction, Fraction]:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def dot3(
    u: tuple[Fraction, Fraction, Fraction], v: tuple[Fraction, Fraction, Fraction]
) -> Fraction:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def sq_norm3(u: tuple[Fraction, Fraction, Fraction]) -> Fraction:
    return dot3(u, u)


def test_quad_contact_newton_euler_and_lorentz_cone() -> None:
    """Verify exact 3D 4-contact bilinear ZMP force/torque balance and Lorentz cone membership."""
    m = Fraction(40, 1)
    g = Fraction(981, 100)
    h_g = Fraction(4, 5)
    w_x = Fraction(1, 4)
    w_y = Fraction(1, 5)
    mu = Fraction(3, 5)

    for ax_num, ay_num in [(-2, 1), (0, 0), (1, -1), (-3, -2)]:
        ax = Fraction(ax_num, 1)
        ay = Fraction(ay_num, 1)
        net_fx = Fraction(0)
        net_fy = Fraction(0)
        net_fz = Fraction(0)
        net_lx = Fraction(0)
        net_ly = Fraction(0)
        net_lz = Fraction(0)

        in_zmp = abs(h_g * ax) <= g * w_x and abs(h_g * ay) <= g * w_y
        in_fric = ax * ax + ay * ay <= (mu * g) ** 2

        for ex in (Fraction(-1), Fraction(1)):
            for ey in (Fraction(-1), Fraction(1)):
                fz = (
                    (m * g / 4)
                    * (1 - ex * (h_g * ax) / (g * w_x))
                    * (1 - ey * (h_g * ay) / (g * w_y))
                )
                fx = (ax / g) * fz
                fy = (ay / g) * fz
                offset = (ex * w_x, ey * w_y, -h_g)
                force = (fx, fy, fz)
                torque = cross3(offset, force)

                net_fx += fx
                net_fy += fy
                net_fz += fz
                net_lx += torque[0]
                net_ly += torque[1]
                net_lz += torque[2]

                if in_zmp and in_fric:
                    assert fz >= 0
                    assert fx * fx + fy * fy <= (mu * fz) ** 2

        assert net_fx == m * ax
        assert net_fy == m * ay
        assert net_fz - m * g == 0
        assert (net_lx, net_ly, net_lz) == (Fraction(0), Fraction(0), Fraction(0))


def test_homography_unit_singular_vector_and_sandwich() -> None:
    """Verify Faugeras-Lustman unit eigenvalue G(n x v) = n x v and Lagrange sandwich identity."""
    # Unit normal n = (3/5, 4/5, 0)
    n = (Fraction(3, 5), Fraction(4, 5), Fraction(0))
    assert sq_norm3(n) == Fraction(1)

    v = (Fraction(1, 2), Fraction(-1, 3), Fraction(2, 5))
    w = cross3(n, v)
    assert dot3(n, w) == 0
    assert dot3(v, w) == 0

    # Gram operator G(x) = x + (v.x) n + (n.x) v + (n.x * ||v||^2) n
    def gram_h(
        x: tuple[Fraction, Fraction, Fraction],
    ) -> tuple[Fraction, Fraction, Fraction]:
        vx = dot3(v, x)
        nx = dot3(n, x)
        v_sq = sq_norm3(v)
        c_n = vx + nx * v_sq
        return (
            x[0] + c_n * n[0] + nx * v[0],
            x[1] + c_n * n[1] + nx * v[1],
            x[2] + c_n * n[2] + nx * v[2],
        )

    assert gram_h(w) == w

    # Check 2D trace and determinant sandwich identity:
    # (s1_sq - 1)*(1 - s3_sq) = (s1_sq + s3_sq) - s1_sq*s3_sq - 1 = ||n x v||^2
    tr_2d = 2 + 2 * dot3(n, v) + sq_norm3(v)
    det_2d = (1 + dot3(n, v)) ** 2
    sandwich_prod = tr_2d - det_2d - 1
    assert sandwich_prod == sq_norm3(w)
    assert sandwich_prod > 0


def test_se3_rotational_depth_cancellation() -> None:
    """Verify that (w x n) . X + n . (w x X) == 0 for arbitrary 3D vectors."""
    w = (Fraction(7, 3), Fraction(-5, 2), Fraction(11, 4))
    n = (Fraction(1, 3), Fraction(2, 3), Fraction(2, 3))
    x_pt = (Fraction(4, 1), Fraction(-2, 5), Fraction(9, 2))
    assert dot3(cross3(w, n), x_pt) + dot3(n, cross3(w, x_pt)) == Fraction(0)


def test_robot_energy_smoothness_pareto_suboptimality() -> None:
    """Verify exact rational integrals I_v(eta), I_a(eta), I_j(eta) and Pareto dominance on [-11, 0)."""

    def i_v(eta: Fraction) -> Fraction:
        return (
            Fraction(3, 10010) * (eta + Fraction(260, 9)) ** 2
            + Fraction(350, 297)
        )

    def i_a(eta: Fraction) -> Fraction:
        return Fraction(2, 77) * (eta + 11) ** 2 + Fraction(14, 1)

    def i_j(eta: Fraction) -> Fraction:
        return 4 * eta**2 + Fraction(720, 1)

    assert i_v(Fraction(0)) == Fraction(10, 7)
    assert i_a(Fraction(0)) == Fraction(120, 7)
    assert i_j(Fraction(0)) == Fraction(720, 1)

    assert i_a(Fraction(-11)) == Fraction(14, 1)
    assert (i_a(Fraction(0)) - i_a(Fraction(-11))) / i_a(Fraction(0)) == Fraction(
        11, 60
    )

    assert i_v(Fraction(-11)) == Fraction(497, 390)
    assert (i_v(Fraction(0)) - i_v(Fraction(-11))) / i_v(Fraction(0)) == Fraction(
        421, 3900
    )

    for eta_val in [Fraction(-11), Fraction(-8), Fraction(-5), Fraction(-1), Fraction(-1, 10)]:
        assert i_a(eta_val) < i_a(Fraction(0))
        assert i_v(eta_val) < i_v(Fraction(0))


def test_world_frame_transport_and_minimal_intervention() -> None:
    """Verify R06 Euler-centripetal orthogonality, R07 nullspace projection, and R03 velocity jump."""
    # R06: unit axis k_hat = (0, 3/5, 4/5)
    k_hat = (Fraction(0), Fraction(3, 5), Fraction(4, 5))
    assert sq_norm3(k_hat) == Fraction(1)
    p = (Fraction(2, 1), Fraction(-1, 2), Fraction(3, 4))
    dtheta = Fraction(3, 2)
    ddtheta = Fraction(5, 3)

    omega = tuple(dtheta * c for c in k_hat)
    alpha = tuple(ddtheta * c for c in k_hat)
    a_euler = cross3(alpha, p)
    a_cent = cross3(omega, cross3(omega, p))
    assert dot3(a_euler, a_cent) == Fraction(0)

    a_comb = (
        a_euler[0] + a_cent[0],
        a_euler[1] + a_cent[1],
        a_euler[2] + a_cent[2],
    )
    assert sq_norm3(a_comb) == (ddtheta**2 + dtheta**4) * sq_norm3(cross3(k_hat, p))
    assert sq_norm3(cross3(k_hat, p)) == sq_norm3(p) - dot3(k_hat, p) ** 2

    # R07: minimal-intervention allocation
    j_vec = (Fraction(1, 1), Fraction(2, 1), Fraction(-2, 1))
    q_nom = (Fraction(1, 3), Fraction(-1, 2), Fraction(3, 4))
    v_task = Fraction(5, 2)
    scale = (v_task - dot3(j_vec, q_nom)) / sq_norm3(j_vec)
    q_star = (
        q_nom[0] + scale * j_vec[0],
        q_nom[1] + scale * j_vec[1],
        q_nom[2] + scale * j_vec[2],
    )
    assert dot3(j_vec, q_star) == v_task

    # Nullspace vector z with J . z == 0
    z_null = (Fraction(2, 1), Fraction(0, 1), Fraction(1, 1))
    assert dot3(j_vec, z_null) == Fraction(0)
    assert dot3(z_null, q_star) == dot3(z_null, q_nom)

    # R03: exact velocity jump across rate 3/2 -> 1/2
    v_left = Fraction(23, 480) * Fraction(3, 2)
    v_right = Fraction(23, 480) * Fraction(1, 2)
    assert v_left == Fraction(23, 320)
    assert v_right == Fraction(23, 960)
    assert v_right - v_left == Fraction(-23, 480)
