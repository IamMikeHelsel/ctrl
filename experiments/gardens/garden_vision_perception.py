"""Garden 2 — Machine Vision & Perception Under Motion.

What conventional baselines discard:
1. Classical 8-point epipolar geometry and two-view ray triangulation assume both camera views are
   captured with zero transport/rolling-shutter skew (delta_t = 0), discarding the translational
   velocity twist v * delta_t that biases epipolar residuals and can flip triangulated depth d < 0.
2. Visual-inertial and homography observability checks invoke O(n^3) floating-point SVD / eigensolvers
   (non-deterministic in hard real-time PLC/C99 loops) to check rank >= 2 excitation.
3. Outlier rejection relies on randomized RANSAC without an algebraic optimality certificate.

What this garden restores in plain sight:
1. Motion-Compensated Epipolar Bilinear Identity & Affine Cheirality Skew Margin:
   x2 . ((t + v * dt) x R x1) = x2 . (t x R x1) + dt * (x2 . (v x R x1)),
   and exact affine depth sensitivity d_i(t + v * dt) = d_i(t) + s_i * dt with sharp cheirality
   flip boundary dt_max = min(d_1(t)/|s_1|, d_2(t)/|s_2|).
2. Lamzouri / Newton-Girard Determinant-Free Gram Excitation Gate:
   (tr G)^2 - tr(G^2) = 2 * sum_{i < j} lambda_i * lambda_j (= 2 * det(G) on 2x2),
   giving exact rational excitation ratio rho_eff(G) = ((tr G)^2 - tr(G^2)) / (tr G)^2 in [0, 1 - 1/n]
   and SPD eigenvalue lower bound lambda_min(G) >= ((tr G)^2 - tr(G^2)) / (2 * tr G) with zero SVD/sqrt.
3. Certifiable Truncated Least Squares (TLS) Perception Duality:
   min_{w_i in [0,1]} sum_i (w_i * r_i^2 + c_bar^2 * (1 - w_i)) == sum_i min(r_i^2, c_bar^2),
   providing an exact rational zero-gap primal-dual certificate separating geometric inliers from outliers.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, Sequence, TypeVar

Number = TypeVar("Number", float, Fraction)
Vec3 = tuple[Number, Number, Number]


def dot3(u: Vec3[Number], v: Vec3[Number]) -> Number:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross3(u: Vec3[Number], v: Vec3[Number]) -> Vec3[Number]:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def add3(u: Vec3[Number], v: Vec3[Number]) -> Vec3[Number]:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def smul3(c: Number, u: Vec3[Number]) -> Vec3[Number]:
    return (c * u[0], c * u[1], c * u[2])


def sq_norm3(u: Vec3[Number]) -> Number:
    return dot3(u, u)


def motion_compensated_epipolar_residual(
    r_x1: Vec3[Number],
    x2: Vec3[Number],
    t_base: Vec3[Number],
    v_vel: Vec3[Number],
    delta_t: Number,
) -> dict[str, Number | bool]:
    """Compute uncompensated and motion-compensated epipolar residuals under baseline t + v * delta_t.

    Exact Bilinear Identity:
        x2 . ((t + v * dt) x R x1) == x2 . (t x R x1) + dt * (x2 . (v x R x1)).
    """
    t_pert = add3(t_base, smul3(delta_t, v_vel))
    uncompensated = dot3(x2, cross3(t_pert, r_x1))
    static_term = dot3(x2, cross3(t_base, r_x1))
    velocity_rate = dot3(x2, cross3(v_vel, r_x1))
    bilinear_rhs = static_term + delta_t * velocity_rate
    compensated = uncompensated - delta_t * velocity_rate
    is_frac = isinstance(delta_t, Fraction)
    exact_match = (
        uncompensated == bilinear_rhs and compensated == static_term
        if is_frac
        else (abs(uncompensated - bilinear_rhs) < 1e-12 and abs(compensated - static_term) < 1e-12)
    )
    return {
        "uncompensated_residual": uncompensated,
        "static_residual": static_term,
        "velocity_epipolar_rate": velocity_rate,
        "compensated_residual": compensated,
        "identity_holds": exact_match,
    }


def triangulate_motion_cheirality_margin(
    r_x1: Vec3[Number],
    x2: Vec3[Number],
    t_base: Vec3[Number],
    v_vel: Vec3[Number],
    delta_t: Number,
) -> dict[str, Number | bool]:
    """Compute two-view triangulation depths (d1, d2) under timestamp skew delta_t and the exact
    rational Cheirality Skew Margin delta_t_crit above which depth flips negative.
    """
    n_vec = cross3(x2, r_x1)
    denom = sq_norm3(n_vec)
    if denom == 0:
        raise ValueError("Parallel rays: x2 x R x1 == 0")

    d1_0 = -dot3(n_vec, cross3(x2, t_base)) / denom
    d2_0 = -dot3(n_vec, cross3(r_x1, t_base)) / denom

    s1 = -dot3(n_vec, cross3(x2, v_vel)) / denom
    s2 = -dot3(n_vec, cross3(r_x1, v_vel)) / denom

    t_pert = add3(t_base, smul3(delta_t, v_vel))
    d1_pert = -dot3(n_vec, cross3(x2, t_pert)) / denom
    d2_pert = -dot3(n_vec, cross3(r_x1, t_pert)) / denom

    d1_affine = d1_0 + delta_t * s1
    d2_affine = d2_0 + delta_t * s2

    # Critical skew bound where min(d1, d2) hits 0:
    bounds: list[Number] = []
    if s1 != 0:
        b1 = d1_0 / abs(s1)  # type: ignore[arg-type]
        bounds.append(b1)
    if s2 != 0:
        b2 = d2_0 / abs(s2)  # type: ignore[arg-type]
        bounds.append(b2)
    dt_crit = min(bounds) if bounds else d1_0

    is_frac = isinstance(delta_t, Fraction)
    zero: Number = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    affine_exact = (
        (d1_pert == d1_affine and d2_pert == d2_affine)
        if is_frac
        else (abs(d1_pert - d1_affine) < 1e-12 and abs(d2_pert - d2_affine) < 1e-12)
    )
    return {
        "d1_static": d1_0,
        "d2_static": d2_0,
        "s1_sensitivity": s1,
        "s2_sensitivity": s2,
        "d1_skewed": d1_pert,
        "d2_skewed": d2_pert,
        "critical_skew_margin": dt_crit,
        "cheirality_preserved": bool(d1_pert > zero and d2_pert > zero),
        "affine_identity_holds": affine_exact,
    }


def lamzouri_gram_excitation_gate(
    g_mat: Sequence[Sequence[Number]],
    rho_min: Number,
) -> dict[str, Number | bool]:
    """Certify persistent excitation of an n x n symmetric Gram matrix G without SVD or square roots.

    Uses the Newton-Girard / Lamzouri identity:
        (tr G)^2 - tr(G^2) == 2 * sum_{1 <= i < j <= n} lambda_i * lambda_j
    which equals 2 * det(G) for 2x2 matrices, and defines the dimensionless excitation ratio:
        rho_eff(G) = ((tr G)^2 - tr(G^2)) / (tr G)^2 in [0, 1 - 1/n].
    For 2x2 PSD matrices, lambda_min(G) >= ((tr G)^2 - tr(G^2)) / (2 * tr G).
    """
    n = len(g_mat)
    if n == 0:
        raise ValueError("Gram matrix must be non-empty")
    is_frac = isinstance(g_mat[0][0], Fraction)
    zero: Number = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    two: Number = Fraction(2, 1) if is_frac else 2.0  # type: ignore[assignment]

    tr_g = zero
    for i in range(n):
        tr_g = tr_g + g_mat[i][i]

    # For symmetric G, tr(G^2) = sum_{i,j} G_{ij}^2 (Frobenius norm squared)
    tr_g2 = zero
    for i in range(n):
        for j in range(n):
            tr_g2 = tr_g2 + g_mat[i][j] * g_mat[j][i]

    dispersion_num = tr_g * tr_g - tr_g2
    if tr_g <= zero:
        return {
            "trace_g": tr_g,
            "trace_g_sq": tr_g2,
            "dispersion_numerator": dispersion_num,
            "rho_eff": zero,
            "lambda_min_lower_bound": zero,
            "excited": False,
        }

    rho_eff = dispersion_num / (tr_g * tr_g)
    lam_min_lb = dispersion_num / (two * tr_g)
    res: dict[str, Number | bool] = {
        "trace_g": tr_g,
        "trace_g_sq": tr_g2,
        "dispersion_numerator": dispersion_num,
        "rho_eff": rho_eff,
        "lambda_min_lower_bound": lam_min_lb,
        "excited": bool(rho_eff >= rho_min and lam_min_lb > zero),
    }
    if n == 2:
        det_2x2 = g_mat[0][0] * g_mat[1][1] - g_mat[0][1] * g_mat[1][0]
        res["two_det_2x2"] = two * det_2x2
        res["newton_girard_2x2_exact"] = (
            dispersion_num == two * det_2x2
            if is_frac
            else abs(dispersion_num - two * det_2x2) < 1e-12
        )
    return res


def certify_tls_perception_duality(
    residuals: Sequence[Number],
    c_bar: Number,
    candidate_weights: Sequence[Number] | None = None,
) -> dict[str, Any]:
    """Compute the exact Truncated Least Squares (TLS) primal-dual perception certificate:
        min_{w_i in [0,1]} sum_i (w_i * r_i^2 + c_bar^2 * (1 - w_i)) == sum_i min(r_i^2, c_bar^2).

    If `candidate_weights` is omitted, constructs the exact optimal dual weights w_i^* in {0, 1}
    with zero duality gap. If suboptimal/corrupted weights are supplied, computes the exact
    nonnegative optimality gap.
    """
    is_frac = isinstance(c_bar, Fraction)
    zero: Number = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]
    one: Number = Fraction(1, 1) if is_frac else 1.0  # type: ignore[assignment]
    c_sq = c_bar * c_bar

    opt_weights: list[Number] = []
    primal_cost = zero
    for r in residuals:
        r_sq = r * r
        if r_sq < c_sq:
            opt_weights.append(one)
            primal_cost = primal_cost + r_sq
        else:
            opt_weights.append(zero)
            primal_cost = primal_cost + c_sq

    weights = list(candidate_weights) if candidate_weights is not None else opt_weights
    dual_surrogate = zero
    decomp_gap = zero
    inlier_indices: list[int] = []
    outlier_indices: list[int] = []

    for idx, (r, w) in enumerate(zip(residuals, weights)):
        if w < zero or w > one:
            raise ValueError(f"TLS weight w[{idx}] = {w} outside [0, 1]")
        r_sq = r * r
        dual_surrogate = dual_surrogate + (w * r_sq + c_sq * (one - w))
        if r_sq < c_sq:
            inlier_indices.append(idx)
            decomp_gap = decomp_gap + (one - w) * (c_sq - r_sq)
        else:
            outlier_indices.append(idx)
            decomp_gap = decomp_gap + w * (r_sq - c_sq)

    raw_gap = dual_surrogate - primal_cost
    exact_zero_gap = (
        (raw_gap == zero and decomp_gap == zero)
        if is_frac
        else (abs(raw_gap) < 1e-12 and abs(decomp_gap) < 1e-12)
    )
    gap_identity_holds = (
        raw_gap == decomp_gap if is_frac else abs(raw_gap - decomp_gap) < 1e-12
    )
    return {
        "primal_tls_cost": primal_cost,
        "dual_surrogate_cost": dual_surrogate,
        "duality_gap": raw_gap,
        "decomposed_gap": decomp_gap,
        "optimal_weights": opt_weights,
        "inlier_indices": inlier_indices,
        "outlier_indices": outlier_indices,
        "certified_optimal": exact_zero_gap,
        "gap_decomposition_exact": gap_identity_holds,
    }


def run_garden_vision_perception() -> dict[str, Any]:
    """Execute all exact-Fraction + float64 experiments and adversarial negative controls for Garden 2."""
    # 1. Motion-Compensated Epipolar & Cheirality Margin
    # True 3D point X = (0, 0, 2) seen from Camera 1 at origin (R=I, x1=(0,0,1))
    # and Camera 2 translated by t_base = (-1, 0, 0) so X_2 = X_1 - t_base?
    # Using ControlsLean.Vision.Triangulation convention: d2 * x2 = d1 * (R x1) + t_base.
    # Let R x1 = (0, 0, 1), d1 = 2, t_base = (1, 0, 0), so d2 * x2 = (1, 0, 2) -> d2 = 1, x2 = (1, 0, 2).
    r_x1_q: Vec3[Fraction] = (Fraction(0), Fraction(0), Fraction(1))
    x2_q: Vec3[Fraction] = (Fraction(1), Fraction(0), Fraction(2))
    t_base_q: Vec3[Fraction] = (Fraction(1), Fraction(0), Fraction(0))
    # Camera 2 moving with velocity v_vel = (-4, 1, 0) during exposure/transport skew delta_t = 1/20 s
    v_vel_q: Vec3[Fraction] = (Fraction(-4), Fraction(1), Fraction(0))
    dt_safe_q = Fraction(1, 20)

    epi_q = motion_compensated_epipolar_residual(r_x1_q, x2_q, t_base_q, v_vel_q, dt_safe_q)
    assert epi_q["static_residual"] == Fraction(0)
    assert epi_q["uncompensated_residual"] != Fraction(0)
    assert epi_q["compensated_residual"] == Fraction(0)
    assert epi_q["identity_holds"] is True

    # Float parity for epipolar compensation
    epi_f = motion_compensated_epipolar_residual(
        (0.0, 0.0, 1.0), (1.0, 0.0, 2.0), (1.0, 0.0, 0.0), (-4.0, 1.0, 0.0), 0.05
    )
    assert epi_f["identity_holds"] is True
    assert abs(float(epi_q["uncompensated_residual"]) - float(epi_f["uncompensated_residual"])) < 1e-15

    # Triangulation cheirality under safe skew vs adversarial skew > critical_skew_margin
    # Use pure baseline velocity v_vel = (-4, 0, 0) so rays stay coplanar while depth shifts affinely
    v_baseline_q: Vec3[Fraction] = (Fraction(-4), Fraction(0), Fraction(0))
    tri_safe_q = triangulate_motion_cheirality_margin(
        r_x1_q, x2_q, t_base_q, v_baseline_q, Fraction(1, 10)
    )
    assert tri_safe_q["d1_static"] == Fraction(2)
    assert tri_safe_q["d2_static"] == Fraction(1)
    assert tri_safe_q["critical_skew_margin"] == Fraction(1, 4)  # 250 ms
    assert tri_safe_q["cheirality_preserved"] is True
    assert tri_safe_q["affine_identity_holds"] is True

    # Adversarial skew delta_t = 3/10 s > 1/4 s flips depth negative!
    tri_flip_q = triangulate_motion_cheirality_margin(
        r_x1_q, x2_q, t_base_q, v_baseline_q, Fraction(3, 10)
    )
    assert tri_flip_q["cheirality_preserved"] is False
    assert tri_flip_q["d1_skewed"] < 0 and tri_flip_q["d2_skewed"] < 0

    # 2. Lamzouri Determinant-Free Gram Excitation Gate (Exact Q + Float64)
    g_excited_q = [
        [Fraction(5, 1), Fraction(2, 1)],
        [Fraction(2, 1), Fraction(3, 1)],
    ]
    gate_exc_q = lamzouri_gram_excitation_gate(g_excited_q, rho_min=Fraction(1, 5))
    assert gate_exc_q["newton_girard_2x2_exact"] is True
    assert gate_exc_q["dispersion_numerator"] == Fraction(22, 1)  # 2 * det([[5,2],[2,3]]) = 2 * 11 = 22
    assert gate_exc_q["rho_eff"] == Fraction(22, 64)  # 11/32 = 0.34375 >= 0.20
    assert gate_exc_q["lambda_min_lower_bound"] == Fraction(11, 8)
    assert gate_exc_q["excited"] is True

    # Adversarial rank-1 degenerate Gram matrix (collinear optical flow features)
    g_rank1_q = [
        [Fraction(4, 1), Fraction(6, 1)],
        [Fraction(6, 1), Fraction(9, 1)],
    ]
    gate_deg_q = lamzouri_gram_excitation_gate(g_rank1_q, rho_min=Fraction(1, 5))
    assert gate_deg_q["dispersion_numerator"] == Fraction(0)
    assert gate_deg_q["rho_eff"] == Fraction(0)
    assert gate_deg_q["excited"] is False

    # 3. Certifiable Truncated Least Squares (TLS) Perception Duality
    # 5 feature residuals: 3 inliers (r_i <= 1/2) and 2 gross outliers (r_i = 4, -5) with c_bar = 1
    residuals_q = [
        Fraction(1, 10),
        Fraction(-1, 5),
        Fraction(4, 1),     # outlier #1
        Fraction(3, 10),
        Fraction(-5, 1),    # outlier #2
    ]
    c_bar_q = Fraction(1, 1)
    tls_opt_q = certify_tls_perception_duality(residuals_q, c_bar_q)
    assert tls_opt_q["certified_optimal"] is True
    assert tls_opt_q["duality_gap"] == Fraction(0)
    assert tls_opt_q["inlier_indices"] == [0, 1, 3]
    assert tls_opt_q["outlier_indices"] == [2, 4]
    assert tls_opt_q["primal_tls_cost"] == Fraction(14, 100) + Fraction(2, 1)  # 0.01 + 0.04 + 0.09 + 2 = 2.14

    # Adversarial naive WLS/RANSAC weight assignment that trusts outlier #1 (w_2 = 1)
    corrupted_weights_q = [
        Fraction(1), Fraction(1), Fraction(1), Fraction(1), Fraction(0)
    ]
    tls_corrupt_q = certify_tls_perception_duality(residuals_q, c_bar_q, corrupted_weights_q)
    assert tls_corrupt_q["certified_optimal"] is False
    assert tls_corrupt_q["duality_gap"] == Fraction(15, 1)  # r_2^2 - c_bar^2 = 16 - 1 = 15 > 0
    assert tls_corrupt_q["gap_decomposition_exact"] is True

    return {
        "garden_id": "vision_perception",
        "title": "Garden 2: Machine Vision & Perception Under Motion",
        "discarded_by_baseline": (
            "Classical epipolar/triangulation pipelines ignore camera velocity twist v * delta_t "
            "during rolling-shutter/transport skew, rely on non-deterministic O(n^3) SVD for "
            "observability gating, and use uncertified randomized outlier rejection."
        ),
        "restored_exact_identities": [
            "x2 . ((t + v*dt) x R x1) == x2 . (t x R x1) + dt * (x2 . (v x R x1)) (Bilinear Motion Epipolar Identity)",
            "d_i(t + v*dt) == d_i(t) - dt * (n . (r_i x v)) / ||n||^2 (Affine Triangulation Skew Sensitivity)",
            "(tr G)^2 - tr(G^2) == 2 * sum_{i<j} lambda_i * lambda_j == 2 * det(G) (Lamzouri SVD-Free Excitation Identity)",
            "sum_i (w_i r_i^2 + c_bar^2 (1 - w_i)) - sum_i min(r_i^2, c_bar^2) == sum_{in} (1-w_i)(c_bar^2-r_i^2) + sum_{out} w_i(r_i^2-c_bar^2)",
        ],
        "metrics": {
            "uncompensated_epipolar_residual_q": str(epi_q["uncompensated_residual"]),
            "motion_compensated_epipolar_residual_q": str(epi_q["compensated_residual"]),
            "triangulation_d1_static_q": str(tri_safe_q["d1_static"]),
            "triangulation_d2_static_q": str(tri_safe_q["d2_static"]),
            "critical_skew_margin_q": str(tri_safe_q["critical_skew_margin"]),
            "critical_skew_margin_ms": round(float(tri_safe_q["critical_skew_margin"]) * 1000.0, 3),
            "lamzouri_excited_rho_eff_q": str(gate_exc_q["rho_eff"]),
            "lamzouri_lambda_min_lb_q": str(gate_exc_q["lambda_min_lower_bound"]),
            "tls_primal_cost_q": str(tls_opt_q["primal_tls_cost"]),
            "tls_optimal_duality_gap_q": str(tls_opt_q["duality_gap"]),
            "tls_inliers_identified": tls_opt_q["inlier_indices"],
            "tls_outliers_rejected": tls_opt_q["outlier_indices"],
        },
        "adversarial_negative_controls": {
            "skew_300ms_exceeds_250ms_margin_flips_cheirality": not bool(tri_flip_q["cheirality_preserved"]),
            "rank1_collinear_gram_rejected_by_lamzouri_gate": not bool(gate_deg_q["excited"]),
            "unrejected_outlier_detected_by_tls_duality_gap_q": str(tls_corrupt_q["duality_gap"]),
        },
        "all_passed": True,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_garden_vision_perception(), indent=2))
