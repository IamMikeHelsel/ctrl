"""Slotine–Li kernel: C99 vs numpy reference, model identities, and the Lean V̇ identity."""

from __future__ import annotations

import re

import numpy as np
import pytest

from ctrl.robotics import planar_rr
from ctrl.robotics import slotine_li as sl
from ctrl.robotics.bench_slotine_li import simulate
from ctrl.robotics.registry import REPO_ROOT, lean_declarations, verify_lean_bindings

LEAN = REPO_ROOT / "ControlsLean/Robotics/ManipulatorTracking.lean"
needs_cc = pytest.mark.skipif(sl.compiler() is None, reason="no C compiler")


def _spd(rng, n, lo=0.5):
    A = rng.normal(size=(n, n))
    return A @ A.T + lo * np.eye(n)


def _case(rng):
    return dict(
        q=rng.uniform(-np.pi, np.pi, 2),
        dq=rng.normal(size=2),
        q_d=rng.uniform(-np.pi, np.pi, 2),
        dq_d=rng.normal(size=2),
        ddq_d=rng.normal(size=2),
        Lam=rng.normal(size=(2, 2)),  # the Lean statements allow any Λ
        Kd=_spd(rng, 2),
        Gamma=_spd(rng, 5),
        theta_hat=rng.normal(size=5),
        g0=float(rng.uniform(0, 12)),
    )


# ------------------------------------------------------------- C vs reference


@needs_cc
def test_c_kernel_matches_reference():
    rng = np.random.default_rng(0)
    for _ in range(500):
        c = _case(rng)
        ref, got = sl.slotine_li_torque(**c), sl.slotine_li_torque_c(**c)
        for name in ("tau", "theta_dot", "s", "dq_r", "ddq_r", "Y"):
            np.testing.assert_allclose(
                getattr(got, name), getattr(ref, name), rtol=1e-12, atol=1e-12, err_msg=name
            )


@needs_cc
def test_c_regressor_matches_reference():
    rng = np.random.default_rng(1)
    for _ in range(200):
        q, dq, v, a = (rng.normal(size=2) for _ in range(4))
        np.testing.assert_allclose(
            sl.regressor_c(q, dq, v, a, 9.81),
            planar_rr.regressor(q, dq, v, a, 9.81),
            rtol=1e-13,
            atol=1e-13,
        )


@needs_cc
def test_c_kernel_rejects_null_tau():
    lib = sl.load_kernel()
    z = np.zeros(25)
    p = z.ctypes.data_as(sl._P)
    assert lib.ctrl_slotine_li_torque(*([p] * 9), 9.81, None, None, None, None, None, None) == -1


def test_c_source_has_no_heap_allocation():
    code = sl.C_SOURCE.read_text()
    assert not re.search(r"\b(malloc|calloc|realloc|free|alloca)\s*\(", code)
    assert "static " not in code  # no hidden state


def test_c_source_cites_real_lean_names():
    src = LEAN.read_text()
    # declarations, plus hypothesis binders such as `(hcl : ...)` of those theorems
    decls = lean_declarations(LEAN) | set(re.findall(r"\((h\w*) :", src))
    text = sl.C_SOURCE.read_text() + sl.C_HEADER.read_text()
    cited = set(re.findall(r"`([A-Za-z_][A-Za-z0-9_]*)`", text)) - {"fk"}
    assert cited, "kernel comments should cite Lean declarations"
    assert cited <= decls, cited - decls


def test_lean_bindings_resolve():
    assert verify_lean_bindings() == []


# ------------------------------------------------------------- sign conventions


def test_sign_conventions_match_lean_definitions():
    rng = np.random.default_rng(2)
    c = _case(rng)
    out = sl.slotine_li_torque(**c)
    e = c["q"] - c["q_d"]  # trackingError
    np.testing.assert_allclose(out.dq_r, c["dq_d"] - c["Lam"] @ e)  # referenceVel
    np.testing.assert_allclose(out.s, c["dq"] - out.dq_r)  # slidingError
    np.testing.assert_allclose(out.s, (c["dq"] - c["dq_d"]) + c["Lam"] @ e)  # _eq_velError_add
    np.testing.assert_allclose(out.tau, out.Y @ c["theta_hat"] - c["Kd"] @ out.s)
    np.testing.assert_allclose(out.theta_dot, -c["Gamma"] @ out.Y.T @ out.s)


# ------------------------------------------------------------- the model


def test_regressor_identity_against_dynamics_model():
    rng = np.random.default_rng(3)
    for _ in range(200):
        theta = rng.normal(size=5)
        q, dq, v, a = (rng.normal(size=2) for _ in range(4))
        lhs = planar_rr.regressor(q, dq, v, a, 9.81) @ theta
        rhs = (
            planar_rr.mass_matrix(theta, q) @ a
            + planar_rr.coriolis(theta, q, dq) @ v
            + planar_rr.gravity(theta, q, 9.81)
        )
        np.testing.assert_allclose(lhs, rhs, rtol=1e-12, atol=1e-12)


def _energies(p: planar_rr.ArmPhysical, q, dq, g0=9.81):
    """Kinetic and potential energy from the PlanarArm `fk` geometry, independently of θ."""
    q1, q12 = q[0], q[0] + q[1]
    w1, w12 = dq[0], dq[0] + dq[1]
    c1 = np.array([p.lc1 * np.cos(q1), p.lc1 * np.sin(q1)])
    v1 = w1 * np.array([-p.lc1 * np.sin(q1), p.lc1 * np.cos(q1)])
    elbow_v = w1 * np.array([-p.l1 * np.sin(q1), p.l1 * np.cos(q1)])
    elbow = np.array([p.l1 * np.cos(q1), p.l1 * np.sin(q1)])
    c2 = elbow + p.lc2 * np.array([np.cos(q12), np.sin(q12)])
    v2 = elbow_v + w12 * p.lc2 * np.array([-np.sin(q12), np.cos(q12)])
    tip = elbow + p.l2 * np.array([np.cos(q12), np.sin(q12)])
    vt = elbow_v + w12 * p.l2 * np.array([-np.sin(q12), np.cos(q12)])
    T = 0.5 * (p.m1 * v1 @ v1 + p.I1 * w1**2 + p.m2 * v2 @ v2 + p.I2 * w12**2)
    T += 0.5 * p.payload * vt @ vt
    U = g0 * (p.m1 * c1[1] + p.m2 * c2[1] + p.payload * tip[1])
    return T, U


def test_model_is_the_lagrangian_of_the_planar_arm():
    rng = np.random.default_rng(4)
    p = planar_rr.ArmPhysical(payload=1.3)
    theta = planar_rr.params_from_physical(p)
    h = 1e-6
    for _ in range(20):
        q, dq = rng.normal(size=2), rng.normal(size=2)
        T, _ = _energies(p, q, dq)
        assert np.isclose(T, 0.5 * dq @ planar_rr.mass_matrix(theta, q) @ dq, rtol=1e-12)
        dU = [
            (_energies(p, q + h * ei, dq)[1] - _energies(p, q - h * ei, dq)[1]) / (2 * h)
            for ei in np.eye(2)
        ]
        np.testing.assert_allclose(planar_rr.gravity(theta, q), dU, rtol=1e-7, atol=1e-7)
        # Christoffel: (C dq)_k = Σ_ij (∂_i M_kj - ½ ∂_k M_ij) dq_i dq_j
        dM = [
            (planar_rr.mass_matrix(theta, q + h * ei) - planar_rr.mass_matrix(theta, q - h * ei))
            / (2 * h)
            for ei in np.eye(2)
        ]
        cdq = [
            sum(
                (dM[i][k, j] - 0.5 * dM[k][i, j]) * dq[i] * dq[j]
                for i in range(2)
                for j in range(2)
            )
            for k in range(2)
        ]
        np.testing.assert_allclose(planar_rr.coriolis(theta, q, dq) @ dq, cdq, atol=1e-7)
        Mdot = sum(dM[i] * dq[i] for i in range(2))
        np.testing.assert_allclose(planar_rr.mass_matrix_dot(theta, q, dq), Mdot, atol=1e-7)


def test_skew_symmetry_hypothesis_holds():
    """`hskew` of the Lean theorems: (Mdot - 2C)ᵀ = -(Mdot - 2C)."""
    rng = np.random.default_rng(5)
    for _ in range(100):
        theta, q, dq = rng.normal(size=5), rng.normal(size=2), rng.normal(size=2)
        N = planar_rr.mass_matrix_dot(theta, q, dq) - 2 * planar_rr.coriolis(theta, q, dq)
        np.testing.assert_allclose(N.T, -N, atol=1e-14)


# ------------------------------------------------------------- the Lyapunov identity


@pytest.mark.parametrize("backend", ["numpy", pytest.param("c", marks=needs_cc)])
def test_closed_loop_meets_lean_hypotheses_and_vdot(backend):
    """At random states with the true plant: `hcl`, `hadapt`, and V̇ = -sᵀK_D s ≤ 0."""
    law = sl.slotine_li_torque_c if backend == "c" else sl.slotine_li_torque
    rng = np.random.default_rng(6)
    arm = planar_rr.ArmPhysical(payload=float(rng.uniform(0, 3)))
    theta = planar_rr.params_from_physical(arm)
    for _ in range(200):
        c = _case(rng)
        c["Lam"] = _spd(rng, 2)
        out = law(**c)
        q, dq, g0 = c["q"], c["dq"], c["g0"]
        ddq = planar_rr.forward_dynamics(theta, q, dq, out.tau, g0)
        s, sdot = out.s, ddq - out.ddq_r
        M = planar_rr.mass_matrix(theta, q)
        C = planar_rr.coriolis(theta, q, dq)
        tt = c["theta_hat"] - theta
        Ginv = np.linalg.inv(c["Gamma"])
        # hcl:  M ṡ + C s + K_D s = Y θ~
        np.testing.assert_allclose(M @ sdot + C @ s + c["Kd"] @ s, out.Y @ tt, atol=1e-9)
        # hadapt:  Γ⁻¹ θ~̇ = -Yᵀ s
        np.testing.assert_allclose(Ginv @ out.theta_dot, -out.Y.T @ s, atol=1e-8)
        Md = planar_rr.mass_matrix_dot(theta, q, dq)
        vdot = 0.5 * s @ Md @ s + s @ M @ sdot + tt @ Ginv @ out.theta_dot
        bound = -s @ c["Kd"] @ s
        assert vdot == pytest.approx(bound, rel=1e-8, abs=1e-8)
        assert vdot <= 1e-9


def test_exact_parameters_give_nonadaptive_identity():
    """`slotine_li_lyapunov_deriv`: with θ̂ = θ and Γ = 0, d/dt ½sᵀMs = -sᵀK_D s."""
    rng = np.random.default_rng(7)
    theta = planar_rr.params_from_physical(planar_rr.ArmPhysical(payload=0.7))
    for _ in range(50):
        c = _case(rng) | {"theta_hat": theta, "Gamma": np.zeros((5, 5))}
        out = sl.slotine_li_torque(**c)
        ddq = planar_rr.forward_dynamics(theta, c["q"], c["dq"], out.tau, c["g0"])
        s, sdot = out.s, ddq - out.ddq_r
        M = planar_rr.mass_matrix(theta, c["q"])
        Md = planar_rr.mass_matrix_dot(theta, c["q"], c["dq"])
        assert 0.5 * s @ Md @ s + s @ M @ sdot == pytest.approx(
            -s @ c["Kd"] @ s, rel=1e-9, abs=1e-9
        )


# ------------------------------------------------------------- benchmark smoke


@pytest.mark.parametrize("backend", ["numpy", pytest.param("c", marks=needs_cc)])
def test_benchmark_smoke(backend):
    kw = dict(T=4.0, dt=2e-3, payload=2.0, backend=backend)
    ad = simulate("adaptive", **kw)
    fixed = simulate("slotine_li_fixed", **kw)
    ctc = simulate("ctc", **kw)
    assert ad.rms_error < fixed.rms_error < ctc.rms_error
    assert ad.theta_error_final < ad.theta_error_initial
    ly = ad.lyapunov
    assert ly["max_pointwise_residual"] < 1e-9
    assert ly["max_V_increase_per_step"] < 1e-9
    assert ly["max_integrated_balance"] < 1e-3 * ly["V0"]
    assert ly["V_final"] < ly["V0"]
