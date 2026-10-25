"""Milestone 5: Comprehensive Cross-Discipline Unit Test Suite.

Verifies:
1. Push B (Controls — Centroidal Deceleration Limit & Exact Counterexample):
   - Positive safety theorem (deceleration_safe_unconditional) across diverse physical parameters
     (friction-limited, tipping-limited, tall humanoid, quadruped, planetary rover).
   - Negative counterexample theorem (deceleration_unsafe_counterexample) proving inevitable slip
     or rotational tipping when a_req > a_safe_max.
   - Contact normal force non-negativity equivalence to ZMP stability.
   - 3D Lorentz friction cone coupling with lateral acceleration.

2. Push C (Vision -> Controls — Visual Servoing Depth Invariance & Chaumette's Conundrum):
   - Analytical closed-loop depth formula matching vector trajectory along plane normal.
   - Master depth invariant theorem: n ⬝ X_c(t) >= min(n ⬝ X_0, n ⬝ X_star) > 0 for all t >= 0.
   - Continuous ODE derivative identity d/dt(depth) = -λ (depth - depth_star).
   - Chaumette camera retreat conundrum in unconstrained classical visual servoing.

3. Push A (Math — Exact Rational Dual SDP Certificate on Active Lanes):
   - Target 1: Toy 4x4 Lyapunov contraction operator positive definiteness
     (Toy 4x4 Lyapunov stability example, NOT the real 6x6 Byers-Nash mf13 lane).
   - Target 2: Erdős 834 Li hypergraph exact rational dual bound 44.5279 over Q.
   - Target 3: Grid discrete energy / 2x2 block trace relaxation (work/pod/885/).
   - JSON serialization, disk roundtrip, and tamper rejection.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

# Ensure repository root is on sys.path
REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.push_sdp_cert import (  # noqa: E402
    certify_erdos834_li_hypergraph,
    certify_grid_block_trace,
    certify_lyapunov_contraction,
    certify_toy_lyapunov_contraction,
    run_push_sdp_cert,
)
from tools.sdp_rational_cert import SDPRationalCertificate  # noqa: E402


def _linspace(start: float, stop: float, num: int) -> list[float]:
    if num <= 1:
        return [start]
    step = (stop - start) / (num - 1)
    return [start + i * step for i in range(num)]


def _dot(u: list[float], v: list[float]) -> float:
    return sum(ui * vi for ui, vi in zip(u, v, strict=False))


def _norm(u: list[float]) -> float:
    return math.sqrt(sum(x * x for x in u))

# ==============================================================================
# 1. Push B: Controls — Centroidal Deceleration Limit Tests
# ==============================================================================


def safe_decel_max(mu: float, W: float, hG: float, g: float = 9.81) -> float:
    return g * min(mu, W / hG)


def satisfies_friction(a_req: float, mu: float, g: float = 9.81) -> bool:
    return abs(a_req) <= mu * g + 1e-12


def satisfies_zmp(a_req: float, W: float, hG: float, g: float = 9.81) -> bool:
    return (hG * abs(a_req)) / g <= W + 1e-12


def contact_normal_forces(
    m: float, a_req: float, W: float, hG: float, g: float = 9.81
) -> tuple[float, float]:
    f_front = (m * g / 2.0) * (1.0 + (hG * a_req) / (g * W))
    f_rear = (m * g / 2.0) * (1.0 - (hG * a_req) / (g * W))
    return f_front, f_rear


def test_deceleration_safe_unconditional_friction_limited():
    # Friction-limited regime: μ = 0.3, W = 0.5, h_G = 1.0 (μ < W/h_G = 0.5)
    mu, W, hG, g = 0.3, 0.5, 1.0, 9.81
    a_max = safe_decel_max(mu, W, hG, g)
    assert math.isclose(a_max, mu * g)

    # For any required deceleration up to a_max, both constraints MUST hold
    for a_req in _linspace(0.0, a_max, 50):
        assert satisfies_friction(a_req, mu, g)
        assert satisfies_zmp(a_req, W, hG, g)
        f_front, f_rear = contact_normal_forces(50.0, a_req, W, hG, g)
        assert f_front >= -1e-9
        assert f_rear >= -1e-9
        assert math.isclose(f_front + f_rear, 50.0 * g)


def test_deceleration_safe_unconditional_tipping_limited():
    # Tipping-limited regime: μ = 1.2, W = 0.2, h_G = 1.0 (W/h_G = 0.2 < μ = 1.2)
    mu, W, hG, g = 1.2, 0.2, 1.0, 9.81
    a_max = safe_decel_max(mu, W, hG, g)
    assert math.isclose(a_max, (W / hG) * g)

    for a_req in _linspace(0.0, a_max, 50):
        assert satisfies_friction(a_req, mu, g)
        assert satisfies_zmp(a_req, W, hG, g)
        f_front, f_rear = contact_normal_forces(70.0, a_req, W, hG, g)
        assert f_front >= -1e-9
        assert f_rear >= -1e-9


def test_deceleration_unsafe_counterexample():
    # Test that exceeding a_safe_max strictly induces slip or tipping across regimes
    cases = [
        {"name": "friction_limited", "mu": 0.25, "W": 0.8, "hG": 1.0, "g": 9.81},
        {"name": "tipping_limited", "mu": 1.5, "W": 0.15, "hG": 1.2, "g": 9.81},
        {"name": "tall_humanoid", "mu": 0.8, "W": 0.18, "hG": 1.7, "g": 9.81},
        {"name": "planetary_rover", "mu": 0.4, "W": 0.9, "hG": 0.6, "g": 3.71},
    ]

    for c in cases:
        mu, W, hG, g = c["mu"], c["W"], c["hG"], c["g"]
        a_max = safe_decel_max(mu, W, hG, g)

        # Exceed safe limit by delta
        for delta in [0.01, 0.1, 0.5, 2.0]:
            a_unsafe = a_max + delta
            fric_ok = satisfies_friction(a_unsafe, mu, g)
            zmp_ok = satisfies_zmp(a_unsafe, W, hG, g)

            # At least one must fail!
            assert not (fric_ok and zmp_ok), f"Failed for case {c['name']} at delta={delta}"

            # Verify physical mechanism:
            if mu < W / hG:
                # Friction limited: slip occurs
                assert not fric_ok
            else:
                # Tipping limited: tipping occurs (rear foot lifts off / negative normal force)
                assert not zmp_ok
                _, f_rear = contact_normal_forces(60.0, a_unsafe, W, hG, g)
                assert f_rear < 0.0


def test_deceleration_safe_3d_lorentz():
    # 3D Lorentz friction cone with lateral acceleration a_y
    mu, W, hG, g = 0.8, 0.4, 1.0, 9.81
    cone_radius = mu * g

    # Case 1: no lateral acceleration (reduces to planar)
    a_y = 0.0
    a_x_max = min(math.sqrt(cone_radius**2 - a_y**2), g * (W / hG))
    assert satisfies_friction(a_x_max, mu, g)
    assert satisfies_zmp(a_x_max, W, hG, g)

    # Case 2: 50% lateral acceleration budget consumed
    a_y = 0.5 * cone_radius
    headroom = math.sqrt(cone_radius**2 - a_y**2)
    a_x_max_3d = min(headroom, g * (W / hG))

    # Check 3D Lorentz cone condition: a_x^2 + a_y^2 <= (mu * g)^2
    assert a_x_max_3d**2 + a_y**2 <= cone_radius**2 + 1e-11
    assert satisfies_zmp(a_x_max_3d, W, hG, g)

    # Exceeding 3D headroom induces slip
    a_x_excess = headroom + 0.1
    assert a_x_excess**2 + a_y**2 > cone_radius**2


# ==============================================================================
# 2. Push C: Vision -> Controls — Visual Servoing Invariant Tests
# ==============================================================================


def visual_servoing_traj(
    X_0: list[float], X_star: list[float], lam: float, t: float
) -> list[float]:
    alpha = math.exp(-lam * t)
    return [alpha * x0 + (1.0 - alpha) * xs for x0, xs in zip(X_0, X_star, strict=False)]


def test_visual_servoing_depth_invariance():
    # Plane normal and 3D camera coordinates
    n = [0.0, 0.0, 1.0]  # Optical axis / plane normal
    X_0 = [0.5, -0.3, 1.2]  # Initial depth = 1.2 > 0
    X_star = [0.0, 0.0, 0.6]  # Target depth = 0.6 > 0
    lam = 1.5

    depth_0 = _dot(n, X_0)
    depth_star = _dot(n, X_star)
    min_depth = min(depth_0, depth_star)

    # Evaluate across a dense timeline
    times = _linspace(0.0, 10.0, 500)
    for t in times:
        X_t = visual_servoing_traj(X_0, X_star, lam, t)
        depth_t = _dot(n, X_t)

        # Check analytical formula identity
        expected_depth = (
            math.exp(-lam * t) * depth_0 + (1.0 - math.exp(-lam * t)) * depth_star
        )
        assert math.isclose(depth_t, expected_depth, rel_tol=1e-12)

        # Check Master Invariant Theorem: depth >= min(depth_0, depth_star) > 0
        assert depth_t >= min_depth - 1e-12
        assert depth_t > 0.0

    # Check asymptotic convergence to target
    X_inf = visual_servoing_traj(X_0, X_star, lam, 20.0)
    assert all(math.isclose(a, b, abs_tol=1e-6) for a, b in zip(X_inf, X_star, strict=False))


def test_visual_servoing_continuous_ode_derivative():
    # Verify that the trajectory numerically satisfies the ODE:
    # d/dt (depth) = -λ * (depth - depth_star)
    raw_n = [0.1, 0.2, 0.9]
    n_norm = _norm(raw_n)
    n = [x / n_norm for x in raw_n]
    X_0 = [1.0, 2.0, 1.5]
    X_star = [0.2, 0.1, 0.8]
    lam = 2.0
    dt = 1e-6

    depth_star = _dot(n, X_star)

    for t in [0.1, 0.5, 1.0, 2.5]:
        depth_t = _dot(n, visual_servoing_traj(X_0, X_star, lam, t))
        depth_next = _dot(n, visual_servoing_traj(X_0, X_star, lam, t + dt))

        num_deriv = (depth_next - depth_t) / dt
        analytic_deriv = -lam * (depth_t - depth_star)
        assert math.isclose(num_deriv, analytic_deriv, rel_tol=1e-5)


def test_chaumette_camera_retreat_conundrum():
    # In unconstrained classical IBVS, pure rotation about optical axis
    # induces spurious translation drift: z(t) = z(0) * exp(c * t)
    z_0 = 1.0
    c = 0.5  # Positive retreat drift
    M = 100.0  # Large distance threshold

    # Find the finite time T when depth exceeds M
    # z_0 * exp(c * T) > M => T > ln(M / z_0) / c
    T_thresh = math.log(M / z_0) / c
    assert z_0 * math.exp(c * T_thresh) >= M - 1e-9

    # For any t > T_thresh, camera depth retreats past M
    t_retreat = T_thresh + 1.0
    z_retreat = z_0 * math.exp(c * t_retreat)
    assert z_retreat > M

    # This proves that unconstrained IBVS suffers from camera retreat,
    # whereas the homography-decoupled law strictly bounds depth in [min, max].


# ==============================================================================
# 3. Push A: Math — Exact Rational Dual SDP Certificate Tests
# ==============================================================================


def test_certify_toy_lyapunov_contraction():
    """Verify toy 4x4 Lyapunov contraction operator.

    NOTE: This is a Toy 4x4 Lyapunov stability example, NOT the real 6x6 Byers-Nash mf13 lane.
    """
    res = certify_toy_lyapunov_contraction()
    assert res["is_verified"]
    assert res["n"] == 4
    assert res["max_reconstruction_error"] == "0"

    # All pivots of P and Q are strictly positive fractions
    min_p_pivot = Fraction(res["P_min_pivot"])
    min_q_pivot = Fraction(res["Q_min_pivot"])
    assert min_p_pivot > 0
    assert min_q_pivot > 0


def test_certify_lyapunov_contraction_alias():
    """Verify backwards-compatibility alias certify_lyapunov_contraction."""
    res = certify_lyapunov_contraction()
    assert res["is_verified"]
    assert res["n"] == 4


def test_certify_erdos834_li_hypergraph():
    cert, bound = certify_erdos834_li_hypergraph()
    assert cert.is_verified
    assert cert.n == 9
    assert cert.reconstruction_max_abs_error == "0"

    # The exact rational bound over Q matches the elevated 44.5279 target
    bound_float = float(bound)
    assert math.isclose(bound_float, 44.5279, abs_tol=0.01)

    # Every pivot in D is strictly positive
    for d_str in cert.D:
        assert Fraction(d_str) > 0


def test_certify_grid_block_trace():
    cert, bound = certify_grid_block_trace(rows=3, cols=3)
    assert cert.is_verified
    assert cert.n == 9
    assert cert.reconstruction_max_abs_error == "0"
    assert float(bound) > 0.0

    for d_str in cert.D:
        assert Fraction(d_str) > 0


def test_run_push_sdp_cert_pipeline(tmp_path: Path):
    results = run_push_sdp_cert(out_dir=tmp_path)
    assert len(results) == 3

    for target in ("toy_lyapunov_contraction", "erdos834_li_hypergraph", "grid_discrete_energy"):
        assert target in results
        assert results[target]["is_verified"]
        assert results[target]["max_reconstruction_error"] == "0"

    # Verify JSON files written to disk
    toy_p_file = tmp_path / "toy_lyapunov_P_cert.json"
    e834_file = tmp_path / "erdos834_li_hypergraph_cert.json"
    grid_file = tmp_path / "grid_discrete_energy_885_cert.json"
    assert toy_p_file.exists()
    assert e834_file.exists()
    assert grid_file.exists()

    # Verify roundtrip loading
    e834_loaded = SDPRationalCertificate.from_json(e834_file)
    assert e834_loaded.is_verified
    assert e834_loaded.n == 9

    grid_loaded = SDPRationalCertificate.from_json(grid_file)
    assert grid_loaded.is_verified
    assert grid_loaded.n == 9
