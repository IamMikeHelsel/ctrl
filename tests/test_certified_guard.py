"""Unit and differential tests for the S12-B01 OSQP/CVXPY exact rational certificate & PLC guard pilot."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import pytest

from ctrl.robotics import (
    CertifiedGuardResult,
    certified_plc_box_guard,
    certify_osqp_safety_filter,
    compile_and_verify_c99_kernels,
    compute_four_support_interval,
    emit_c99_and_iec61131,
    verify_farkas_box_certificate,
    verify_lean_bindings,
)


def test_four_support_interval_soundness_and_f09_fixture() -> None:
    """Verify exact 4-support interval [u_min, u_max] on S12 F09 and endpoint/convex soundness."""
    wl = Fraction(27, 70)
    wu = Fraction(47, 80)
    bl = Fraction(9, 10)
    bu = Fraction(11, 10)
    alpha = Fraction(1, 8)
    beta = Fraction(3, 4)

    iv = compute_four_support_interval(wl, wu, bl, bu, alpha, beta)
    assert iv["nonempty"] is True
    assert iv["u_min"] == Fraction(-143, 280)
    assert iv["u_max"] == Fraction(-37, 80)
    assert iv["width"] == Fraction(27, 560)
    assert iv["corners_safe"] is True

    # Nominal F09 action u = -1/2 lies inside [-13/20, -37/80] = [-0.65, -0.4625]
    u_cmd = Fraction(-1, 2)
    assert iv["u_min"] <= u_cmd <= iv["u_max"]

    # Double consumption u = -1 lies strictly outside [-13/20, -37/80]
    assert not (iv["u_min"] <= Fraction(-1, 1) <= iv["u_max"])

    # Verify four_support_interval_sound across grid of (w, b, rho, u)
    for w_val in (wl, (wl + wu) / 2, wu):
        for b_val in (bl, (bl + bu) / 2, bu):
            for u_val in (iv["u_min"], u_cmd, iv["u_max"]):
                assert -alpha <= w_val + u_val <= alpha
                assert -beta <= b_val + u_val <= beta
                for rho in (Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)):
                    mix = (1 - rho) * (w_val + u_val) + rho * (b_val + u_val)
                    assert -beta <= mix <= beta

    # Float mode parity
    iv_f = compute_four_support_interval(
        float(wl), float(wu), float(bl), float(bu), float(alpha), float(beta)
    )
    assert iv_f["nonempty"] is True
    assert abs(iv_f["u_min"] - float(iv["u_min"])) < 1e-15
    assert abs(iv_f["u_max"] - float(iv["u_max"])) < 1e-15

    # Invalid support bounds or alpha > beta raise ValueError
    with pytest.raises(ValueError, match="wl <= wu"):
        compute_four_support_interval(Fraction(1), Fraction(0), bl, bu, alpha, beta)
    with pytest.raises(ValueError, match="alpha <= beta"):
        compute_four_support_interval(wl, wu, bl, bu, Fraction(1), Fraction(1, 2))


def test_farkas_box_infeasibility_certificate_exact_and_forged() -> None:
    """Verify exact rational Farkas infeasibility witness for A u <= b, l <= u <= u_max."""
    # System: u_0 + u_1 <= -3 with box bounds 0 <= u_0 <= 2, 0 <= u_1 <= 2 (infeasible)
    a_mat = [[Fraction(1), Fraction(1)]]
    b_vec = [Fraction(-3)]
    l_vec = [Fraction(0), Fraction(0)]
    u_max = [Fraction(2), Fraction(2)]

    # Dual multiplier y = [1], z_lo = [1, 1], z_hi = [0, 0]
    # Stationarity: A^T y + z_hi - z_lo = [1, 1] + [0, 0] - [1, 1] = [0, 0]
    # RHS: (-3)*1 + 0 - 0 = -3 < 0
    cert = verify_farkas_box_certificate(
        a_mat,
        b_vec,
        l_vec,
        u_max,
        y_dual=[Fraction(1)],
        z_lo=[Fraction(1), Fraction(1)],
        z_hi=[Fraction(0), Fraction(0)],
    )
    assert cert["valid"] is True
    assert cert["stationarity_residual"] == Fraction(0)
    assert cert["farkas_rhs"] == Fraction(-3)

    # Auto-reconstructed z_lo, z_hi from y_dual alone
    cert_auto = verify_farkas_box_certificate(a_mat, b_vec, l_vec, u_max, y_dual=[Fraction(1)])
    assert cert_auto["valid"] is True
    assert cert_auto["stationarity_residual"] == Fraction(0)
    assert cert_auto["farkas_rhs"] == Fraction(-3)

    # Forged certificate with negative y_dual -> rejected
    cert_neg = verify_farkas_box_certificate(a_mat, b_vec, l_vec, u_max, y_dual=[Fraction(-1)])
    assert cert_neg["valid"] is False

    # Feasible system b = [3] cannot be certified infeasible by y = [1]
    cert_feas = verify_farkas_box_certificate(
        a_mat, [Fraction(3)], l_vec, u_max, y_dual=[Fraction(1)]
    )
    assert cert_feas["valid"] is False
    assert cert_feas["farkas_rhs"] == Fraction(3)


def test_certify_osqp_safety_filter_outcomes_and_mutations() -> None:
    """Verify accepted, rejected_certificate, and inconclusive_reconstruction outcomes."""
    a_mat = [[1, 1], [1, -1]]
    b_vec = [1, 0]
    l_vec = [-1, -1]
    u_max = [1, 1]
    fallback = [Fraction(0), Fraction(0)]

    # 1. Exact rational primal feasible candidate -> accepted
    res_acc = certify_osqp_safety_filter(
        a_mat,
        b_vec,
        l_vec,
        u_max,
        u_candidate=[Fraction(1, 4), Fraction(1, 2)],
        u_fallback=fallback,
    )
    assert isinstance(res_acc, CertifiedGuardResult)
    assert res_acc.status == "accepted"
    assert res_acc.certificate_type == "primal_feasible"
    assert res_acc.primal_residual_margin == Fraction(1, 4)
    assert res_acc.u_certified == (Fraction(1, 4), Fraction(1, 2))
    assert len(res_acc.model_sha256) == 64
    assert len(res_acc.certificate_sha256) == 64

    # 2. Live OSQP solve on feasible QP with 4-support bounds -> accepted
    res_osqp = certify_osqp_safety_filter(
        a_mat,
        b_vec,
        l_vec,
        u_max,
        u_nominal=[-0.48, 0.2],
        u_fallback=fallback,
        support_bounds=(Fraction(27, 70), Fraction(47, 80), Fraction(9, 10), Fraction(11, 10)),
        alpha=Fraction(1, 8),
        beta=Fraction(3, 4),
        solve_with_osqp=True,
    )
    assert res_osqp.status == "accepted"
    assert res_osqp.certificate_type == "four_support_interval"
    assert res_osqp.safe_correction_interval == (Fraction(-143, 280), Fraction(-37, 80))
    assert Fraction(-143, 280) <= res_osqp.u_certified[0] <= Fraction(-37, 80)

    # 3. Active-set vertex repair vs. inconclusive_reconstruction on tight boundary
    # Constraint: 3 u_0 + 7 u_1 <= 1, -3 u_0 - 7 u_1 <= -1 (exact line 3 u_0 + 7 u_1 == 1)
    a_tight = [[3, 7], [-3, -7]]
    b_tight = [1, -1]
    # Float approximation (0.33331, 0.0) has limit_denominator(10000) == 3332/9997,
    # violating -3 u_0 - 7 u_1 <= -1 by 1/9997 (~1e-4) unless active-set repair is enabled
    res_inconc = certify_osqp_safety_filter(
        a_tight,
        b_tight,
        [0, 0],
        [1, 1],
        u_candidate=[0.33331, 0.0],
        max_denominator=10000,
        allow_active_set_repair=False,
    )
    assert res_inconc.status == "inconclusive_reconstruction"
    assert res_inconc.u_certified == (Fraction(0), Fraction(0))

    res_repaired = certify_osqp_safety_filter(
        a_tight,
        b_tight,
        [0, 0],
        [1, 1],
        u_candidate=[0.33331, 0.0],
        max_denominator=10000,
        allow_active_set_repair=True,
    )
    assert res_repaired.status == "accepted"
    assert 3 * res_repaired.u_certified[0] + 7 * res_repaired.u_certified[1] == Fraction(1)

    # 4. Infeasible safety filter certified via Farkas witness & live OSQP -> accepted fallback
    a_infeas = [[1, 1]]
    b_infeas = [-3]
    res_farkas = certify_osqp_safety_filter(
        a_infeas,
        b_infeas,
        [0, 0],
        [2, 2],
        u_fallback=[Fraction(0), Fraction(0)],
        solve_with_osqp=True,
    )
    assert res_farkas.status == "accepted"
    assert res_farkas.certificate_type == "farkas_infeasible"
    assert res_farkas.farkas_stationarity_residual == Fraction(0)
    assert res_farkas.farkas_rhs_margin < 0
    assert res_farkas.u_certified == (Fraction(0), Fraction(0))

    # 5. Semantic mutations -> rejected_certificate
    res_bad_sha = certify_osqp_safety_filter(
        a_mat,
        b_vec,
        l_vec,
        u_max,
        u_candidate=[Fraction(0), Fraction(0)],
        expected_model_sha256="0" * 64,
    )
    assert res_bad_sha.status == "rejected_certificate"
    assert res_bad_sha.reason == "model_sha256_mismatch"

    res_viol = certify_osqp_safety_filter(
        a_mat,
        b_vec,
        l_vec,
        u_max,
        u_candidate=[Fraction(9, 10), Fraction(9, 10)],
    )
    assert res_viol.status == "rejected_certificate"
    assert res_viol.primal_residual_margin < 0


def test_idempotent_plc_box_guard_and_c99_st_codegen(tmp_path: Path) -> None:
    """Verify idempotent PLC box guard semantics, ST FB emission, and C99 parity."""
    wl = Fraction(27, 70)
    wu = Fraction(47, 80)
    bl = Fraction(9, 10)
    bu = Fraction(11, 10)
    alpha = Fraction(1, 8)
    beta = Fraction(3, 4)
    base_sp = Fraction(2, 1)
    u_cmd = Fraction(-1, 2)
    u_fb = Fraction(0, 1)

    # Repeated scans on identical snapshot must produce identical absolute setpoint
    scan1 = certified_plc_box_guard(
        True, True, 7, 7, wl, wu, bl, bu, alpha, beta, base_sp, u_cmd, u_fb
    )
    scan2 = certified_plc_box_guard(
        True, True, 7, 7, wl, wu, bl, bu, alpha, beta, base_sp, u_cmd, u_fb
    )
    assert scan1["accepted"] is True
    assert scan1 == scan2
    assert scan1["setpoint_out"] == Fraction(3, 2)

    # Stale version or unverified receipt falls back to base_sp + u_fb
    stale = certified_plc_box_guard(
        True, True, 7, 8, wl, wu, bl, bu, alpha, beta, base_sp, u_cmd, u_fb
    )
    assert stale["accepted"] is False
    assert stale["setpoint_out"] == base_sp + u_fb

    unverified = certified_plc_box_guard(
        False, True, 7, 7, wl, wu, bl, bu, alpha, beta, base_sp, u_cmd, u_fb
    )
    assert unverified["accepted"] is False
    assert unverified["setpoint_out"] == base_sp + u_fb

    # Check emitted C99 and IEC 61131-3 ST contain the new guard symbols
    paths = emit_c99_and_iec61131(tmp_path)
    assert "ctrl_certified_box_guard" in paths["header"].read_text()
    assert "FB_CtrlCertifiedGuard" in paths["st_source"].read_text()

    c99 = compile_and_verify_c99_kernels()
    assert c99["compiled_ok"] is True
    assert c99["parity_verified"] is True

    audit = verify_lean_bindings()
    assert audit["ok"] is True
    assert audit["missing_theorems"] == []
