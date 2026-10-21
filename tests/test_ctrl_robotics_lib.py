"""Comprehensive test suite for ctrl.robotics and the unified lean/Robotics Lake library."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import numpy as np

from ctrl import robotics


def test_lean_theorem_registry_and_manifest_audit() -> None:
    """Every public ctrl.robotics function must have valid @lean_theorem bindings with 0 sorry."""
    audit = robotics.verify_lean_bindings()
    assert audit["ok"], f"Lean binding audit failed: {audit}"
    assert audit["missing_theorems"] == []
    assert audit["forbidden_hits"] == []
    assert audit["registered_functions"] >= 28
    assert audit["total_lean_theorems_bound"] >= 110
    assert audit["robotics_lean_modules"] >= 53
    assert audit["robotics_lean_lines"] >= 20000


def test_septic_trajectory_dual_mode_and_pareto_dominance() -> None:
    """Verify exact Q vs. float64 septic trajectory profiles, boundaries, and energy integrals."""
    for eta_q in (Fraction(0, 1), Fraction(-11, 1), Fraction(-5, 1)):
        assert robotics.septic_q(eta_q, Fraction(0, 1)) == Fraction(0, 1)
        assert robotics.septic_q(eta_q, Fraction(1, 1)) == Fraction(1, 1)
        assert robotics.septic_v(eta_q, Fraction(0, 1)) == Fraction(0, 1)
        assert robotics.septic_v(eta_q, Fraction(1, 1)) == Fraction(0, 1)
        assert robotics.septic_a(eta_q, Fraction(0, 1)) == Fraction(0, 1)
        assert robotics.septic_a(eta_q, Fraction(1, 1)) == Fraction(0, 1)

        for s_q in (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)):
            q_exact = robotics.septic_q(eta_q, s_q)
            v_exact = robotics.septic_v(eta_q, s_q)
            a_exact = robotics.septic_a(eta_q, s_q)
            j_exact = robotics.septic_j(eta_q, s_q)

            assert abs(float(q_exact) - robotics.septic_q(float(eta_q), float(s_q))) < 1e-13
            assert abs(float(v_exact) - robotics.septic_v(float(eta_q), float(s_q))) < 1e-13
            assert abs(float(a_exact) - robotics.septic_a(float(eta_q), float(s_q))) < 1e-12
            assert abs(float(j_exact) - robotics.septic_j(float(eta_q), float(s_q))) < 1e-11

    ia_0 = robotics.septic_accel_integral(Fraction(0, 1))
    ia_11 = robotics.septic_accel_integral(Fraction(-11, 1))
    iv_0 = robotics.septic_velocity_integral(Fraction(0, 1))
    iv_11 = robotics.septic_velocity_integral(Fraction(-11, 1))
    ij_0 = robotics.septic_jerk_integral(Fraction(0, 1))

    assert ia_0 == Fraction(120, 7)
    assert ia_11 == Fraction(14, 1)
    assert (ia_0 - ia_11) / ia_0 == Fraction(11, 60)
    assert iv_0 == Fraction(10, 7)
    assert iv_11 == Fraction(497, 390)
    assert (iv_0 - iv_11) / iv_0 == Fraction(421, 3900)
    assert ij_0 == Fraction(720, 1)

    m = Fraction(2, 1)
    b = Fraction(1, 5)
    r_el = Fraction(1, 2)
    kt = Fraction(1, 8)
    disp = Fraction(3, 2)
    dur = Fraction(4, 5)
    e_min_jerk = robotics.electromechanical_energy(m, b, r_el, kt, disp, dur, Fraction(0, 1))
    e_opt = robotics.electromechanical_energy(m, b, r_el, kt, disp, dur, Fraction(-11, 1))
    assert e_opt < e_min_jerk

    eta_star_q = robotics.optimal_septic_eta(m, b, r_el, kt, dur, clamp_monotone=True)
    assert eta_star_q == Fraction(-11, 1)

    v_w, a_w, j_w = robotics.timewarp_derivatives(
        Fraction(2, 1),
        Fraction(3, 1),
        Fraction(4, 1),
        Fraction(1, 2),
        Fraction(1, 3),
        Fraction(1, 5),
    )
    assert v_w == Fraction(1, 1)
    assert a_w == Fraction(2, 3) + Fraction(3, 4)
    assert j_w == Fraction(2, 5) + Fraction(3, 2) + Fraction(1, 2)


def test_quadruped_contact_wrench_and_lorentz_cbf_dual_mode() -> None:
    """Verify exact Q and float64 4-contact bilinear ZMP allocation and Lorentz-cone CBF."""
    p_q = robotics.CentroidalQuadParams(
        m=Fraction(40, 1),
        g=Fraction(981, 100),
        h_g=Fraction(45, 100),
        w_x=Fraction(1, 4),
        w_y=Fraction(18, 100),
        mu=Fraction(3, 5),
    )
    a_safe = robotics.safe_decel_max(p_q.g, p_q.mu, p_q.w_x, p_q.h_g)
    assert a_safe == Fraction(981, 100) * Fraction(5, 9)  # 0.25/0.45 = 5/9 < 3/5

    for ax_num, ay_num in [(-2, 1), (0, 0), (2, -1), (-4, -2)]:
        ax = Fraction(ax_num, 1)
        ay = Fraction(ay_num, 1)
        bal = robotics.verify_quad_wrench_balance(p_q, ax, ay)
        assert bal["net_force_minus_gravity"] == bal["expected_force"]
        assert bal["net_torque"] == (Fraction(0), Fraction(0), Fraction(0))
        assert bal["all_in_lorentz_cone"] is True

    a_cbf = (Fraction(-1, 1), Fraction(0, 1), Fraction(0, 1))
    u_nom = (Fraction(2, 1), Fraction(1, 2), Fraction(981, 100))
    pi_b = (Fraction(-4, 1), Fraction(0, 1), Fraction(981, 100))
    b_req = Fraction(5, 2)
    lam, u_safe = robotics.lorentz_cbf_safety_filter(a_cbf, b_req, u_nom, pi_b)
    assert Fraction(0) <= lam <= Fraction(1)
    assert robotics.in_lorentz_cone(Fraction(3, 5), u_safe)
    assert (a_cbf[0] * u_safe[0] + a_cbf[1] * u_safe[1] + a_cbf[2] * u_safe[2]) == b_req


def test_world_frame_transport_ik_and_realtime_rta() -> None:
    """Verify world-frame transport orthogonality, redundant IK Pythagorean optimality, and RTA."""
    k_hat = (Fraction(0), Fraction(3, 5), Fraction(4, 5))
    p = (Fraction(2, 1), Fraction(-1, 2), Fraction(3, 4))
    dtheta = Fraction(3, 2)
    ddtheta = Fraction(5, 3)

    a_eul = robotics.euler_accel(k_hat, p, ddtheta)
    a_cent = robotics.centripetal_accel(k_hat, p, dtheta)
    assert sum(a_eul[i] * a_cent[i] for i in range(3)) == Fraction(0)

    a_tot = robotics.world_frame_accel(
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        k_hat,
        p,
        dtheta,
        ddtheta,
    )
    sq_tot = sum(c * c for c in a_tot)
    assert sq_tot == robotics.rotational_transport_sq_norm(k_hat, p, dtheta, ddtheta)

    j_row = (Fraction(1), Fraction(2), Fraction(-2))
    q_nom = (Fraction(1, 3), Fraction(-1, 2), Fraction(3, 4))
    v_task = Fraction(5, 2)
    q_star = robotics.minimal_intervention_ik(j_row, q_nom, v_task)
    assert sum(j_row[i] * q_star[i] for i in range(3)) == v_task

    # Alternative task-feasible velocity q_alt = q_star + z_null where J . z_null = 0
    z_null = (Fraction(2), Fraction(0), Fraction(1))
    q_alt = (q_star[0] + z_null[0], q_star[1] + z_null[1], q_star[2] + z_null[2])
    pyth = robotics.verify_pythagorean_ik_optimality(j_row, q_nom, q_alt, v_task)
    assert pyth["lhs_sq_norm"] == pyth["rhs_sum"]
    assert pyth["star_sq_norm"] < pyth["lhs_sq_norm"]

    fk = robotics.two_link_fk_and_jacobian(0.6, 0.4, 0.5, 0.8)
    assert abs(float(fk["r_sq"]) - float(fk["r_sq_cosine_law"])) < 1e-14
    assert fk["in_annulus"] is True

    assert robotics.max_retained_events(Fraction(10, 1), Fraction(1, 4)) == 41
    assert robotics.response_time_analysis(3, [(1, 4), (2, 6)], 12) == 10
    assert robotics.response_time_analysis(6, [(1, 4), (2, 6)], 12) is None


def test_vision_homography_triangulation_and_se3_hbvs() -> None:
    """Verify Faugeras unit singular vector sandwich, chirality elimination, and triangulation."""
    n = (Fraction(3, 5), Fraction(4, 5), Fraction(0))
    v = (Fraction(1, 2), Fraction(-1, 3), Fraction(2, 5))
    sand = robotics.verify_homography_singular_sandwich(n, v)
    assert sand["is_exact"] is True

    surv = robotics.filter_faugeras_chirality_branches(
        Fraction(2, 1), Fraction(3, 1), Fraction(1, 1), Fraction(4, 1)
    )
    assert surv == [(1, 1, 1), (-1, 1, 1)]

    se3_d = robotics.se3_depth_derivative(
        (Fraction(1, 2), Fraction(-3, 4), Fraction(2, 1)),
        (Fraction(1, 3), Fraction(2, 3), Fraction(2, 3)),
        (Fraction(1, 5), Fraction(-2, 5), Fraction(3, 5)),
        (Fraction(7, 3), Fraction(-5, 2), Fraction(11, 4)),
    )
    assert se3_d["rotational_lie_derivative"] == Fraction(0)
    assert se3_d["total_depth_derivative"] == se3_d["translational_formula"]

    hbvs = robotics.hbvs_vs_ibvs_depth_ratio(2.2, 1.0, 2.0, 0.4, np.deg2rad(160.0))
    assert hbvs["hbvs_stays_bounded"] is True
    assert hbvs["ibvs_midpoint_depth"] > 5.0

    # Two-view triangulation: d2 * x2 = d1 * (R x1) + t
    r_x1 = (Fraction(1, 1), Fraction(0, 1), Fraction(2, 1))
    x2 = (Fraction(0, 1), Fraction(1, 1), Fraction(1, 1))
    d1_true = Fraction(3, 1)
    d2_true = Fraction(5, 1)
    t_vec = (
        d2_true * x2[0] - d1_true * r_x1[0],
        d2_true * x2[1] - d1_true * r_x1[1],
        d2_true * x2[2] - d1_true * r_x1[2],
    )
    d1_rec, d2_rec = robotics.triangulate_two_view_rays(r_x1, x2, t_vec)
    assert (d1_rec, d2_rec) == (d1_true, d2_true)


def test_estimation_lqr_dare_kalman_kalata_luenberger_mpc() -> None:
    """Verify DARE completion of squares, Joseph Kalman MMSE, Kalata tracker, Luenberger, and MPC."""
    a_mat = np.array([[1.0, 0.1], [0.0, 0.95]])
    b_mat = np.array([[0.005], [0.1]])
    q_mat = np.eye(2)
    r_mat = np.array([[0.5]])
    p_mat = np.array([[2.5, 0.4], [0.4, 1.2]])
    k_cand = np.array([[0.8, 1.5]])

    dare = robotics.dare_bellman_completion_of_squares(a_mat, b_mat, q_mat, r_mat, p_mat, k_cand)
    assert dare["max_abs_error"] < 1e-14

    c_obs = np.array([[1.0, 0.0]])
    r_noise = np.array([[0.25]])
    k_est_cand = np.array([[0.6], [0.2]])
    jos = robotics.joseph_kalman_update(p_mat, c_obs, r_noise, k_est_cand)
    assert jos["max_abs_error"] < 1e-14
    assert jos["trace_star"] < jos["trace_cand"]

    kal = robotics.kalata_alpha_beta_gains(0.05, 4.0, 0.01)
    assert 0.0 < kal["alpha"] < 1.0
    assert 0.0 < kal["beta"] <= 2.0 * kal["alpha"]
    assert kal["kalata_quadratic_residual"] < 1e-14

    l_gain = np.array([[0.7], [0.3]])
    luen = robotics.luenberger_separation_step(
        a_mat,
        b_mat,
        c_obs,
        dare["k_star"],
        l_gain,
        np.array([1.2, -0.4]),
        np.array([0.9, -0.1]),
    )
    assert luen["error_step_residual"] < 1e-14
    assert luen["det_separation_residual"] < 1e-14

    # Solve exact discrete Riccati P_inf for terminal CLF in MPC
    p_iter = q_mat.copy()
    for _ in range(150):
        res = robotics.dare_bellman_completion_of_squares(
            a_mat, b_mat, q_mat, r_mat, p_iter, np.zeros((1, 2))
        )
        p_iter = res["dare_tp"]
    k_inf = robotics.dare_bellman_completion_of_squares(
        a_mat, b_mat, q_mat, r_mat, p_iter, np.zeros((1, 2))
    )["k_star"]
    u_seq = np.array([[-0.3], [-0.2], [-0.1], [0.0]])
    mpc = robotics.mpc_warm_start_cost_descent(
        a_mat, b_mat, q_mat, r_mat, p_iter, k_inf, np.array([0.8, 0.2]), u_seq
    )
    assert mpc["shift_identity_error"] < 1e-13
    assert mpc["lyapunov_descent_holds"] is True


def test_c99_and_iec61131_codegen_and_mujoco_benchmarks(tmp_path: Path) -> None:
    """Verify C99 clang compilation + ctypes parity, ST output, and all 3 MuJoCo physics rollouts."""
    emitted = robotics.emit_c99_and_iec61131(tmp_path)
    assert emitted["header"].is_file()
    assert emitted["c_source"].is_file()
    assert emitted["st_source"].is_file()
    assert "FUNCTION_BLOCK FB_CTRL_QUAD_WRENCH_CBF" in emitted["st_source"].read_text()

    c99_check = robotics.compile_and_verify_c99_kernels()
    assert c99_check["compiled_ok"] is True
    assert c99_check["parity_verified"] is True
    assert c99_check["max_c99_vs_python_error"] < 1e-13

    mj = robotics.run_all_mujoco_benchmarks()
    assert mj["ok"] is True
    assert mj["arm_6dof"]["joule_dynamic_reduction_pct"] > 15.0
    assert mj["arm_6dof"]["viscous_reduction_pct"] > 10.0
    assert mj["quad_zmp_cbf"]["safety_verified"] is True
    assert mj["se3_visual_servoing"]["hbvs_monotone_in_interval"] is True
