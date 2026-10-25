"""Garden 3 — Reconciliation of Errors (Multi-Sensor Precision Decomposition & Fault Isolation).

What conventional baselines discard:
1. Naive sensor fusion computes the weighted average x_hat = (sum w_i y_i) / (sum w_i) and discards
   the residual quadratic form J* = sum w_i (y_i - x_hat)^2, failing to notice that J* is identically
   the precision-weighted pairwise disagreement energy (1 / W) * sum_{i < j} w_i w_j (y_i - y_j)^2.
2. Fixed-timeout sensor fusion treats a 99 ms old measurement with the same weight as a 1 ms old
   measurement and then abruptly drops it at 100 ms, causing discontinuous control kicks.
3. Unchecked weighted averaging lets a single spoofed or slipping sensor (e.g. wheel encoder slip on
   ice) drag the fused state outside the safety envelope.

What this garden restores in plain sight:
1. Exact Lagrange-Gauss Precision-Weighted Reconciliation Identity:
   W * sum_{i=1}^m w_i (y_i - x)^2 == W^2 * (x_hat - x)^2 + sum_{1 <= i < j <= m} w_i w_j (y_i - y_j)^2.
   Setting x = x_hat proves that the WLS residual sum of squares is identically the pairwise
   disagreement energy:
   sum_{i=1}^m w_i (y_i - x_hat)^2 == (1 / W) * sum_{1 <= i < j <= m} w_i w_j (y_i - y_j)^2.
2. Staleness-Aware Precision Downweighting:
   w_i(Delta t_i) = 1 / (sigma_i^2 + sigma_a^2 * Delta t_i^2), smoothly decaying stale sensor
   influence as age grows.
3. Certifiable Pairwise Quorum Fault Isolation:
   Honest sensors with |y_i - x| <= eps_i must satisfy |y_i - y_j| <= eps_i + eps_j. Any sensor k
   violating |y_k - y_j| > eps_k + eps_j against a quorum of peers is algebraically isolated and
   excised before fusion, preserving the certified error bound |x_hat_clean - x| <= sum(w_i eps_i)/W_clean.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any, Sequence, TypeVar

Number = TypeVar("Number", float, Fraction)


def staleness_precision_weight(
    sigma_sq: Number, sigma_accel_sq: Number, age_dt: Number
) -> Number:
    """Compute exact staleness-inflated precision weight w_i(dt) = 1 / (sigma_i^2 + sigma_a^2 * dt^2)."""
    one: Number = Fraction(1, 1) if isinstance(sigma_sq, Fraction) else 1.0  # type: ignore[assignment]
    eff_var = sigma_sq + sigma_accel_sq * (age_dt * age_dt)
    if eff_var <= 0:
        raise ValueError("Effective variance must be strictly positive")
    return one / eff_var


def precision_weighted_reconciliation(
    measurements: Sequence[Number],
    weights: Sequence[Number],
    x_truth: Number | None = None,
) -> dict[str, Any]:
    """Compute the precision-weighted fused estimate x_hat and verify the exact Lagrange-Gauss
    reconciliation decomposition into estimation error + pairwise disagreement energy.
    """
    m = len(measurements)
    if m == 0 or len(weights) != m:
        raise ValueError("Measurements and weights must have matching non-zero length")
    is_frac = isinstance(measurements[0], Fraction)
    zero: Number = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]

    w_total = zero
    wy_sum = zero
    for y_i, w_i in zip(measurements, weights):
        if w_i <= zero:
            raise ValueError("Precision weights must be strictly positive")
        w_total = w_total + w_i
        wy_sum = wy_sum + w_i * y_i

    x_hat = wy_sum / w_total

    # Residual sum of squares at x_hat: J* = sum_i w_i * (y_i - x_hat)^2
    rss_at_xhat = zero
    for y_i, w_i in zip(measurements, weights):
        diff = y_i - x_hat
        rss_at_xhat = rss_at_xhat + w_i * (diff * diff)

    # Pairwise disagreement quadratic form: P = sum_{i < j} w_i * w_j * (y_i - y_j)^2
    pairwise_num = zero
    per_sensor_disagreement: list[Number] = [zero for _ in range(m)]
    for i in range(m):
        for j in range(i + 1, m):
            dy = measurements[i] - measurements[j]
            term = weights[i] * weights[j] * (dy * dy)
            pairwise_num = pairwise_num + term
        for j in range(m):
            dy_ij = measurements[i] - measurements[j]
            per_sensor_disagreement[i] = (
                per_sensor_disagreement[i] + weights[j] * (dy_ij * dy_ij)
            )

    pairwise_energy = pairwise_num / w_total
    rss_matches_pairwise = (
        rss_at_xhat == pairwise_energy
        if is_frac
        else abs(rss_at_xhat - pairwise_energy) < 1e-12
    )

    result: dict[str, Any] = {
        "x_hat": x_hat,
        "w_total": w_total,
        "rss_at_xhat": rss_at_xhat,
        "pairwise_disagreement_energy": pairwise_energy,
        "pairwise_numerator": pairwise_num,
        "per_sensor_disagreement": per_sensor_disagreement,
        "rss_equals_pairwise_exact": rss_matches_pairwise,
    }

    if x_truth is not None:
        lhs_total_err = zero
        for y_i, w_i in zip(measurements, weights):
            d_i = y_i - x_truth
            lhs_total_err = lhs_total_err + w_i * (d_i * d_i)
        est_err_term = w_total * ((x_hat - x_truth) * (x_hat - x_truth))
        rhs_decomp = est_err_term + pairwise_energy
        # Also check clearing-denominators polynomial identity:
        # W * sum w_i (y_i - x)^2 == (sum w_i (y_i - x))^2 + sum_{i<j} w_i w_j (y_i - y_j)^2
        poly_lhs = w_total * lhs_total_err
        poly_rhs = (wy_sum - w_total * x_truth) ** 2 + pairwise_num
        decomp_exact = (
            (lhs_total_err == rhs_decomp and poly_lhs == poly_rhs)
            if is_frac
            else (abs(lhs_total_err - rhs_decomp) < 1e-12 and abs(poly_lhs - poly_rhs) < 1e-12)
        )
        result["lhs_total_error_wrt_truth"] = lhs_total_err
        result["estimation_error_term"] = est_err_term
        result["decomposition_wrt_truth_exact"] = decomp_exact

    return result


def reconcile_and_isolate_faults(
    measurements: Sequence[Number],
    base_variances: Sequence[Number],
    ages_dt: Sequence[Number],
    error_bounds_eps: Sequence[Number],
    sigma_accel_sq: Number,
) -> dict[str, Any]:
    """Perform staleness-aware precision weighting and exact pairwise quorum fault isolation.

    Any sensor i whose pairwise difference |y_i - y_j| > eps_i + eps_j against a strict majority
    of peer sensors (or >= 2 peers in a >= 3 sensor bank) is isolated as faulty/spoofed.
    """
    m = len(measurements)
    if not (len(base_variances) == len(ages_dt) == len(error_bounds_eps) == m) or m < 3:
        raise ValueError("Require at least 3 sensors with matching parameter lengths")

    is_frac = isinstance(measurements[0], Fraction)
    zero: Number = Fraction(0, 1) if is_frac else 0.0  # type: ignore[assignment]

    weights = [
        staleness_precision_weight(s_sq, sigma_accel_sq, dt)
        for s_sq, dt in zip(base_variances, ages_dt)
    ]

    # Naive fusion (no fault isolation)
    naive_rec = precision_weighted_reconciliation(measurements, weights)

    # Pairwise consistency matrix: violation[i][j] = True iff |y_i - y_j| > eps_i + eps_j
    conflict_counts: list[int] = [0 for _ in range(m)]
    conflict_pairs: list[tuple[int, int, Number, Number]] = []
    for i in range(m):
        for j in range(i + 1, m):
            diff_ij = abs(measurements[i] - measurements[j])  # type: ignore[arg-type]
            thresh_ij = error_bounds_eps[i] + error_bounds_eps[j]
            if diff_ij > thresh_ij:
                conflict_counts[i] += 1
                conflict_counts[j] += 1
                conflict_pairs.append((i, j, diff_ij, thresh_ij))

    # A sensor conflicting with >= 2 peers (in a bank where honest sensors pairwise agree) is isolated
    isolated_fault_indices = [i for i, cnt in enumerate(conflict_counts) if cnt >= 2]
    healthy_indices = [i for i in range(m) if i not in isolated_fault_indices]

    clean_meas = [measurements[i] for i in healthy_indices]
    clean_weights = [weights[i] for i in healthy_indices]
    clean_eps = [error_bounds_eps[i] for i in healthy_indices]

    clean_rec = precision_weighted_reconciliation(clean_meas, clean_weights)
    w_clean_total = clean_rec["w_total"]
    certified_err_bound = zero
    for w_i, e_i in zip(clean_weights, clean_eps):
        certified_err_bound = certified_err_bound + w_i * e_i
    certified_err_bound = certified_err_bound / w_clean_total

    return {
        "weights": weights,
        "naive_x_hat": naive_rec["x_hat"],
        "naive_pairwise_energy": naive_rec["pairwise_disagreement_energy"],
        "conflict_counts": conflict_counts,
        "isolated_fault_indices": isolated_fault_indices,
        "healthy_indices": healthy_indices,
        "clean_x_hat": clean_rec["x_hat"],
        "clean_pairwise_energy": clean_rec["pairwise_disagreement_energy"],
        "certified_error_bound": certified_err_bound,
    }


def run_garden_error_reconciliation() -> dict[str, Any]:
    """Execute all exact-Fraction + float64 experiments and adversarial negative controls for Garden 3."""
    # 1. Exact Lagrange-Gauss Precision-Weighted Reconciliation Decomposition
    x_truth_q = Fraction(10, 1)
    y_healthy_q = [
        Fraction(1002, 100),  # 10.02 m (LiDAR)
        Fraction(997, 100),   # 9.97 m  (Stereo Vision)
        Fraction(1004, 100),  # 10.04 m (Wheel Odometry)
        Fraction(995, 100),   # 9.95 m  (Radar)
    ]
    w_healthy_q = [Fraction(25, 1), Fraction(16, 1), Fraction(10, 1), Fraction(9, 1)]
    rec_q = precision_weighted_reconciliation(y_healthy_q, w_healthy_q, x_truth=x_truth_q)
    assert rec_q["rss_equals_pairwise_exact"] is True
    assert rec_q["decomposition_wrt_truth_exact"] is True

    # Float64 parity check
    rec_f = precision_weighted_reconciliation(
        [float(y) for y in y_healthy_q],
        [float(w) for w in w_healthy_q],
        x_truth=float(x_truth_q),
    )
    assert rec_f["rss_equals_pairwise_exact"] is True
    assert rec_f["decomposition_wrt_truth_exact"] is True
    assert abs(float(rec_q["x_hat"]) - float(rec_f["x_hat"])) < 1e-14

    # 2. Staleness-Aware Precision Downweighting & Spoofed Wheel-Slip Fault Isolation
    # Suppose Sensor 2 (Wheel Odometry) slips on ice and reports 12.50 m (+2.50 m glitch!)
    y_faulty_q = [
        Fraction(1002, 100),  # Sensor 0: LiDAR (fresh, age = 10 ms)
        Fraction(997, 100),   # Sensor 1: Stereo Vision (age = 20 ms)
        Fraction(1250, 100),  # Sensor 2: Wheel Odometry SLIP GLITCH (12.50 m!)
        Fraction(995, 100),   # Sensor 3: Radar (stale, age = 100 ms)
    ]
    base_vars_q = [
        Fraction(1, 2500),    # sigma = 0.02 m
        Fraction(1, 1600),    # sigma = 0.025 m
        Fraction(1, 1600),    # sigma = 0.025 m
        Fraction(1, 900),     # sigma = 0.033 m
    ]
    ages_q = [
        Fraction(1, 100),     # 10 ms
        Fraction(1, 50),      # 20 ms
        Fraction(1, 100),     # 10 ms
        Fraction(1, 10),      # 100 ms (stale radar downweighted!)
    ]
    eps_bounds_q = [
        Fraction(1, 20),      # 0.05 m
        Fraction(3, 50),      # 0.06 m
        Fraction(3, 50),      # 0.06 m (declared bound violated by slip!)
        Fraction(2, 25),      # 0.08 m
    ]
    sigma_a_sq_q = Fraction(4, 1)  # sigma_a = 2 m/s^2

    iso_q = reconcile_and_isolate_faults(
        y_faulty_q, base_vars_q, ages_q, eps_bounds_q, sigma_a_sq_q
    )

    assert iso_q["isolated_fault_indices"] == [2]
    assert iso_q["healthy_indices"] == [0, 1, 3]

    naive_err_q = abs(iso_q["naive_x_hat"] - x_truth_q)
    clean_err_q = abs(iso_q["clean_x_hat"] - x_truth_q)
    assert clean_err_q <= iso_q["certified_error_bound"]
    assert naive_err_q > Fraction(1, 2)  # Naive fusion dragged > 0.70 m off truth!
    assert clean_err_q < Fraction(2, 100)  # Clean reconciled estimate within 20 mm of truth!
    assert iso_q["naive_pairwise_energy"] > 1000 * iso_q["clean_pairwise_energy"]

    return {
        "garden_id": "error_reconciliation",
        "title": "Garden 3: Reconciliation of Errors & Pairwise Disagreement Certificates",
        "discarded_by_baseline": (
            "Naive WLS/Kalman fusion averages sensor readings without checking the pairwise "
            "disagreement quadratic form (1/W) sum_{i<j} w_i w_j (y_i - y_j)^2, uses step-function "
            "timeouts instead of continuous staleness variance inflation, and allows a single "
            "slipping/spoofed sensor to corrupt the fused state."
        ),
        "restored_exact_identities": [
            "W * sum_i w_i (y_i - x)^2 == W^2 (x_hat - x)^2 + sum_{i<j} w_i w_j (y_i - y_j)^2 (Lagrange-Gauss Reconciliation Identity)",
            "J*(y) = sum_i w_i (y_i - x_hat)^2 == (1/W) sum_{i<j} w_i w_j (y_i - y_j)^2 (Residual-to-Pairwise Energy Identity)",
            "w_i(Delta t_i) = (sigma_i^2 + sigma_a^2 Delta t_i^2)^{-1} (Continuous Staleness Precision Decay)",
            "|x_hat_clean - x| <= (sum_{i in H} w_i eps_i) / (sum_{i in H} w_i) (Quorum-Isolated Error Bound)",
        ],
        "metrics": {
            "healthy_x_hat_q": str(rec_q["x_hat"]),
            "healthy_rss_q": str(rec_q["rss_at_xhat"]),
            "healthy_pairwise_energy_q": str(rec_q["pairwise_disagreement_energy"]),
            "lagrange_gauss_identity_exact": rec_q["decomposition_wrt_truth_exact"],
            "isolated_fault_sensors": iso_q["isolated_fault_indices"],
            "clean_reconciled_x_hat_q": str(iso_q["clean_x_hat"]),
            "clean_estimation_error_mm": round(float(clean_err_q) * 1000.0, 4),
            "certified_error_bound_mm": round(float(iso_q["certified_error_bound"]) * 1000.0, 4),
            "naive_corrupted_error_mm": round(float(naive_err_q) * 1000.0, 4),
            "error_reduction_factor": round(float(naive_err_q / clean_err_q), 2),
        },
        "adversarial_negative_controls": {
            "spoofed_wheel_slip_2p5m_dragged_naive_fusion_beyond_bound": naive_err_q > iso_q["certified_error_bound"],
            "pairwise_disagreement_energy_ratio_fault_vs_clean": round(
                float(iso_q["naive_pairwise_energy"] / iso_q["clean_pairwise_energy"]), 2
            ),
            "quorum_isolator_recovered_certified_bound": clean_err_q <= iso_q["certified_error_bound"],
        },
        "all_passed": True,
    }


if __name__ == "__main__":
    import json

    print(json.dumps(run_garden_error_reconciliation(), indent=2))
