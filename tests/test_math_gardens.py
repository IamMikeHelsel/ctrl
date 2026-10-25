"""Unit, property, and adversarial negative-control tests for the 5 Experimental Math Gardens
and the `ctrl.robotics.orchestration_reconciliation` Lean 4 bridge.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from ctrl.robotics import (  # noqa: E402
    compile_and_verify_c99_kernels,
    decoupled_cone_barrier_and_deriv,
    gram2_effective_rank_gate,
    motion_compensated_epipolar_and_cheirality,
    orchestrate_multi_rate_control,
    precision_reconcile_sensors,
    stop_go_hysteresis_envelope,
    tls_primal_dual_certificate,
    transient_lag_stopping_envelope,
    verify_lean_bindings,
)
from experiments.gardens import (  # noqa: E402
    run_garden_control_orchestration,
    run_garden_discovery_engine,
    run_garden_error_reconciliation,
    run_garden_stopping_going,
    run_garden_vision_perception,
)


def test_lean_bindings_include_orchestration_and_reconciliation() -> None:
    """Verify 100% of @lean_theorem bindings pass against lean/ with 0 sorry/admit."""
    audit = verify_lean_bindings(REPO_ROOT)
    assert audit["ok"] is True
    assert audit["missing_theorems"] == []
    assert audit["forbidden_hits"] == []
    assert audit["registered_functions"] >= 61
    assert audit["total_lean_theorems_bound"] >= 338


def test_transient_lag_and_hysteresis_dual_mode() -> None:
    """Verify exact Fraction and float64 parity for transientLagSaving_eq and stop/go hysteresis."""
    env_q = transient_lag_stopping_envelope(
        w_speed=Fraction(7, 5),
        tau_delay=Fraction(1, 4),
        tau_act=Fraction(1, 10),
        a_max=Fraction(3, 2),
        b_min=Fraction(5, 2),
    )
    assert env_q["identity_holds"] is True
    assert env_q["clearance_saving"] > 0

    env_f = transient_lag_stopping_envelope(1.4, 0.25, 0.10, 1.5, 2.5)
    assert env_f["identity_holds"] is True
    assert abs(float(env_q["clearance_saving"]) - float(env_f["clearance_saving"])) < 1e-15

    hyst_q = stop_go_hysteresis_envelope(
        d_safe=Fraction(1, 2),
        w_speed=Fraction(1, 1),
        tau_delay=Fraction(1, 5),
        tau_act=Fraction(1, 20),
        a_max=Fraction(1, 1),
        b_min=Fraction(2, 1),
        delta_hyst=Fraction(1, 10),
        headway=Fraction(95, 100),
    )
    assert hyst_q["hysteresis_gap"] == Fraction(1, 10)
    assert hyst_q["in_hysteresis_band"] is True
    assert hyst_q["mode"] == "HOLD_HYSTERESIS_BAND"


def test_decoupled_cone_barrier_no_tangential_leakage() -> None:
    """Verify decoupled normal-tangential barrier and zero tangential credit leakage."""
    res_q = decoupled_cone_barrier_and_deriv(
        r_clear=Fraction(2, 1),
        d_safe=Fraction(1, 2),
        v_n=Fraction(-2, 1),
        v_tx=Fraction(0, 1),
        v_ty=Fraction(0, 1),
        a_n=Fraction(-4, 1),
        a_tx=Fraction(3, 1),
        a_ty=Fraction(-2, 1),
        c_n=Fraction(4, 1),
        c_t=Fraction(5, 1),
        mu=Fraction(4, 5),
    )
    assert res_q["is_safe"] is True
    # At v_t = (0, 0) and a_n = -c_n, Lie derivative v_n - v_n*a_n/c_n == -2 - (-2)*(-4)/4 == -4
    assert res_q["barrier_deriv"] == Fraction(-4, 1)


def test_precision_reconcile_sensors_lagrange_identity() -> None:
    """Verify exact Lagrange-Gauss pairwise reconciliation identity in Q and float64."""
    y_q = [Fraction(1002, 100), Fraction(997, 100), Fraction(1004, 100), Fraction(995, 100)]
    w_q = [Fraction(25, 1), Fraction(16, 1), Fraction(10, 1), Fraction(9, 1)]
    rec_q = precision_reconcile_sensors(y_q, w_q, x_candidate=Fraction(10, 1))
    assert rec_q["lagrange_pairwise_identity_exact"] is True
    assert rec_q["weighted_innovation_sum"] == Fraction(0)

    rec_f = precision_reconcile_sensors(
        [float(y) for y in y_q], [float(w) for w in w_q], x_candidate=10.0
    )
    assert rec_f["lagrange_pairwise_identity_exact"] is True
    assert abs(float(rec_q["reconciled_estimate"]) - float(rec_f["reconciled_estimate"])) < 1e-14


def test_orchestrate_multi_rate_and_vision_reconciliation() -> None:
    """Verify 3-tier orchestrator, motion epipolar/cheirality shift, TLS duality, and Gram2 gate."""
    orch_q = orchestrate_multi_rate_control(
        u_nom=Fraction(2, 1),
        u_safe=Fraction(-3, 1),
        u_stop=Fraction(-6, 1),
        lam_cbf=Fraction(3, 5),
        alpha_stop=Fraction(1, 4),
        u_min=Fraction(-6, 1),
        u_max=Fraction(3, 1),
        v0_lyap=Fraction(1, 2),
        rho_cascade=Fraction(4, 5),
        eps_cascade=Fraction(1, 10),
        n_steps=8,
    )
    assert orch_q["u_cbf"] == Fraction(-1, 1)
    assert orch_q["u_orch"] == Fraction(-9, 4)
    assert orch_q["box_invariant"] is True
    assert orch_q["cascade_iss_bound"] == Fraction(1, 2)

    epi_q = motion_compensated_epipolar_and_cheirality(
        r_x1=(Fraction(0), Fraction(0), Fraction(1)),
        x2=(Fraction(1), Fraction(0), Fraction(2)),
        t_base=(Fraction(1), Fraction(0), Fraction(0)),
        v_vel=(Fraction(-4), Fraction(0), Fraction(0)),
        delta_t=Fraction(1, 10),
    )
    assert epi_q["identities_exact"] is True
    assert epi_q["cheirality_positive"] is True

    tls_q = tls_primal_dual_certificate(
        residuals=[Fraction(1, 10), Fraction(-1, 5), Fraction(4, 1)],
        c_bar=Fraction(1, 1),
    )
    assert tls_q["duality_gap"] == Fraction(0)
    assert tls_q["optimal_weights"] == [Fraction(1), Fraction(1), Fraction(0)]
    assert tls_q["primal_le_dual"] is True
    assert tls_q["primal_le_unweighted"] is True

    gram_q = gram2_effective_rank_gate(Fraction(5, 1), Fraction(2, 1), Fraction(3, 1))
    assert gram_q["newton_girard_identity_exact"] is True
    assert gram_q["certified_posdef"] is True
    assert gram_q["det"] == Fraction(11, 1)


def test_all_five_gardens_and_c99_differential_parity() -> None:
    """Execute all 5 Experimental Gardens and verify C99 kernel parity."""
    g1 = run_garden_stopping_going()
    g2 = run_garden_vision_perception()
    g3 = run_garden_error_reconciliation()
    g4 = run_garden_control_orchestration()
    g5 = run_garden_discovery_engine()

    for g in (g1, g2, g3, g4, g5):
        assert g["all_passed"] is True

    c99 = compile_and_verify_c99_kernels()
    assert c99["compiled_ok"] is True
    assert c99["parity_verified"] is True
