"""OSQP/CVXPY exact rational certificate checker and idempotent PLC command guard (S12-B01 pilot).

Implements the bounded library pilot recommended in ``library-opportunities.md``:
1. Accepts a candidate control/QP solution or solver output (from OSQP, CVXPY, SciPy, or direct
   floating-point / rational vectors) for a linear/quadratic safety filter ``A u <= b``,
   ``l <= u <= u_max``.
2. Reconstructs exact ``fractions.Fraction`` primal feasibility witnesses (with optional exact
   active-set basis repair) or exact rational Farkas infeasibility certificates, and computes
   the 4-support static command-correction interval ``[u_min, u_max]``.
3. Returns a structured ``CertifiedGuardResult`` with status in
   ``{"accepted", "rejected_certificate", "inconclusive_reconstruction"}``, exact rational
   residual margins, canonical SHA-256 digests of the model/constraints and certificate, and
   a safe fallback command.
"""

from __future__ import annotations

import hashlib
import itertools
import json
import math
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Literal, TypeVar

import numpy as np

from ctrl.robotics.registry import lean_theorem

T = TypeVar("T", float, Fraction)
CertifiedGuardStatus = Literal[
    "accepted", "rejected_certificate", "inconclusive_reconstruction"
]


@dataclass(frozen=True)
class CertifiedGuardResult:
    """Structured result of exact rational safety-filter certificate verification."""

    status: CertifiedGuardStatus
    certificate_type: str
    u_certified: tuple[Fraction, ...]
    u_fallback: tuple[Fraction, ...]
    u_output_float: tuple[float, ...]
    primal_residual_margin: Fraction
    farkas_stationarity_residual: Fraction
    farkas_rhs_margin: Fraction
    support_bounds: tuple[Fraction, Fraction, Fraction, Fraction] | None
    safe_correction_interval: tuple[Fraction, Fraction] | None
    model_sha256: str
    certificate_sha256: str
    reason: str

    def to_dict(self) -> dict[str, Any]:
        """Serialize the guard result to a JSON-compatible dictionary."""
        return {
            "status": self.status,
            "certificate_type": self.certificate_type,
            "u_certified": [str(v) for v in self.u_certified],
            "u_fallback": [str(v) for v in self.u_fallback],
            "u_output_float": list(self.u_output_float),
            "primal_residual_margin": str(self.primal_residual_margin),
            "farkas_stationarity_residual": str(self.farkas_stationarity_residual),
            "farkas_rhs_margin": str(self.farkas_rhs_margin),
            "support_bounds": (
                [str(v) for v in self.support_bounds]
                if self.support_bounds is not None
                else None
            ),
            "safe_correction_interval": (
                [str(v) for v in self.safe_correction_interval]
                if self.safe_correction_interval is not None
                else None
            ),
            "model_sha256": self.model_sha256,
            "certificate_sha256": self.certificate_sha256,
            "reason": self.reason,
        }

    def __getitem__(self, key: str) -> Any:
        return getattr(self, key)


def _canonical_sha256(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _to_fraction(val: int | float | str | Fraction, max_denominator: int = 10000) -> Fraction:
    if isinstance(val, bool):
        raise ValueError("Boolean is not a valid numeric value.")
    if isinstance(val, Fraction):
        return val
    if isinstance(val, (int, str)):
        return Fraction(val)
    if isinstance(val, (float, np.floating, np.integer)):
        fval = float(val)
        if not math.isfinite(fval):
            raise ValueError(f"Non-finite floating-point value: {val!r}")
        return Fraction(fval).limit_denominator(max_denominator)
    raise ValueError(f"Unsupported numeric type: {type(val)!r}")


def _solve_exact_linear_system(
    matrix: Sequence[Sequence[Fraction]], rhs: Sequence[Fraction]
) -> tuple[Fraction, ...] | None:
    """Solve an exact k x k linear system over Q via Gaussian elimination."""
    n = len(rhs)
    if n == 0 or len(matrix) != n or any(len(row) != n for row in matrix):
        return None
    aug = [
        [Fraction(x) for x in row] + [Fraction(b_val)]
        for row, b_val in zip(matrix, rhs, strict=True)
    ]
    for col in range(n):
        pivot = next((i for i in range(col, n) if aug[i][col] != 0), None)
        if pivot is None:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        piv_val = aug[col][col]
        aug[col] = [x / piv_val for x in aug[col]]
        for row_idx in range(n):
            if row_idx != col and aug[row_idx][col] != 0:
                factor = aug[row_idx][col]
                aug[row_idx] = [
                    x - factor * y for x, y in zip(aug[row_idx], aug[col], strict=True)
                ]
    return tuple(row[-1] for row in aug)


@lean_theorem(
    "Research.TransportCertificate",
    ("fourSupportLower", "fourSupportUpper", "four_support_interval_sound"),
    domain="certified_guard",
    summary=(
        "Four-support static command-correction interval [u_min, u_max] and endpoint "
        "convex-combination safety soundness."
    ),
)
def compute_four_support_interval(
    wl: T,
    wu: T,
    bl: T,
    bu: T,
    alpha: T,
    beta: T,
) -> dict[str, Any]:
    """Compute the 4-support static certified command-correction interval [u_min, u_max].

    Backed by ``Research.TransportCertificate.four_support_interval_sound``:
    - ``u_min = max(-alpha - wl, -beta - bl)``
    - ``u_max = min(alpha - wu, beta - bu)``
    """
    if wl > wu or bl > bu:
        raise ValueError("Support bounds must satisfy wl <= wu and bl <= bu.")
    if alpha < 0 or beta < 0 or alpha > beta:
        raise ValueError("Safety limits must satisfy 0 <= alpha <= beta.")
    u_min: T = max(-alpha - wl, -beta - bl)
    u_max: T = min(alpha - wu, beta - bu)
    nonempty = bool(u_min <= u_max)
    u_mid: T | None = None
    corners_safe = False
    if nonempty:
        two: T = Fraction(2, 1) if isinstance(u_min, Fraction) else 2.0  # type: ignore[assignment]
        u_mid = (u_min + u_max) / two
        corners_safe = bool(
            (-alpha <= wl + u_mid <= alpha)
            and (-alpha <= wu + u_mid <= alpha)
            and (-beta <= bl + u_mid <= beta)
            and (-beta <= bu + u_mid <= beta)
        )
    return {
        "u_min": u_min,
        "u_max": u_max,
        "nonempty": nonempty,
        "width": u_max - u_min,
        "u_midpoint": u_mid,
        "corners_safe": corners_safe,
    }


@lean_theorem(
    "Research.TransportCertificate",
    ("lp_dual_upper_bound", "farkas_box_infeasibility_certificate"),
    domain="certified_guard",
    summary=(
        "Exact rational Farkas infeasibility certificate checker for linear halfspace "
        "and box safety constraints A u <= b, l <= u <= u_max."
    ),
)
def verify_farkas_box_certificate(
    a_mat: Sequence[Sequence[int | float | str | Fraction]],
    b_vec: Sequence[int | float | str | Fraction],
    l_vec: Sequence[int | float | str | Fraction],
    u_max_vec: Sequence[int | float | str | Fraction],
    y_dual: Sequence[int | float | str | Fraction],
    z_lo: Sequence[int | float | str | Fraction] | None = None,
    z_hi: Sequence[int | float | str | Fraction] | None = None,
    *,
    max_denominator: int = 10000,
) -> dict[str, Any]:
    """Verify an exact rational Farkas infeasibility witness for ``A u <= b, l <= u <= u_max``.

    Checks the hypotheses of ``Research.TransportCertificate.farkas_box_infeasibility_certificate``:
    1. ``y >= 0``, ``z_lo >= 0``, ``z_hi >= 0``
    2. ``A^T y + z_hi - z_lo == 0``
    3. ``b^T y + u_max^T z_hi - l^T z_lo < 0``

    If ``z_lo`` and ``z_hi`` are omitted, they are canonically reconstructed from
    ``r = -A^T y`` via ``z_hi_j = max(r_j, 0)`` and ``z_lo_j = max(-r_j, 0)`` so that
    stationarity ``A^T y + z_hi - z_lo == 0`` holds identically.
    """
    m = len(b_vec)
    n = len(l_vec)
    if m == 0 or n == 0 or len(a_mat) != m or any(len(row) != n for row in a_mat):
        raise ValueError("Invalid matrix/vector dimensions for Farkas certificate.")
    if len(u_max_vec) != n or len(y_dual) != m:
        raise ValueError("Box bound or dual vector length mismatch.")

    a_q = [[_to_fraction(v, max_denominator) for v in row] for row in a_mat]
    b_q = [_to_fraction(v, max_denominator) for v in b_vec]
    l_q = [_to_fraction(v, max_denominator) for v in l_vec]
    umax_q = [_to_fraction(v, max_denominator) for v in u_max_vec]
    y_q = [_to_fraction(v, max_denominator) for v in y_dual]

    at_y = [
        sum((y_q[i] * a_q[i][j] for i in range(m)), Fraction(0))
        for j in range(n)
    ]

    if z_lo is None and z_hi is None:
        z_hi_q = [max(-at_y[j], Fraction(0)) for j in range(n)]
        z_lo_q = [max(at_y[j], Fraction(0)) for j in range(n)]
    else:
        if z_lo is None or z_hi is None or len(z_lo) != n or len(z_hi) != n:
            raise ValueError("Both z_lo and z_hi must be length-n sequences when specified.")
        z_lo_q = [_to_fraction(v, max_denominator) for v in z_lo]
        z_hi_q = [_to_fraction(v, max_denominator) for v in z_hi]

    nonneg_ok = (
        all(w >= 0 for w in y_q)
        and all(w >= 0 for w in z_lo_q)
        and all(w >= 0 for w in z_hi_q)
    )
    stat_vec = [at_y[j] + z_hi_q[j] - z_lo_q[j] for j in range(n)]
    stat_res = max((abs(v) for v in stat_vec), default=Fraction(0))
    rhs_val = (
        sum((y_q[i] * b_q[i] for i in range(m)), Fraction(0))
        + sum((z_hi_q[j] * umax_q[j] for j in range(n)), Fraction(0))
        - sum((z_lo_q[j] * l_q[j] for j in range(n)), Fraction(0))
    )
    valid = bool(nonneg_ok and stat_res == 0 and rhs_val < 0)
    return {
        "valid": valid,
        "nonneg_ok": nonneg_ok,
        "stationarity_residual": stat_res,
        "farkas_rhs": rhs_val,
        "y_q": tuple(y_q),
        "z_lo_q": tuple(z_lo_q),
        "z_hi_q": tuple(z_hi_q),
    }


def _primal_margin(
    a_q: list[list[Fraction]],
    b_q: list[Fraction],
    l_q: list[Fraction],
    umax_q: list[Fraction],
    u_q: Sequence[Fraction],
) -> Fraction:
    """Compute min(b_i - (A u)_i, u_j - l_j, u_max_j - u_j); >= 0 iff u_q is feasible."""
    m = len(b_q)
    n = len(l_q)
    margins: list[Fraction] = []
    for i in range(m):
        au_i = sum((a_q[i][j] * u_q[j] for j in range(n)), Fraction(0))
        margins.append(b_q[i] - au_i)
    for j in range(n):
        margins.append(u_q[j] - l_q[j])
        margins.append(umax_q[j] - u_q[j])
    return min(margins)


def _attempt_active_set_primal_repair(
    a_q: list[list[Fraction]],
    b_q: list[Fraction],
    l_q: list[Fraction],
    umax_q: list[Fraction],
    u_float: Sequence[float],
    pool_limit: int = 12,
) -> tuple[Fraction, ...] | None:
    """Attempt exact rational vertex reconstruction from near-active halfspace + box rows."""
    n = len(l_q)
    # Build combined inequality list C u <= d from A u <= b, -u <= -l, u <= u_max
    rows_c: list[list[Fraction]] = list(a_q)
    rows_d: list[Fraction] = list(b_q)
    for j in range(n):
        unit_neg = [Fraction(-1 if k == j else 0) for k in range(n)]
        rows_c.append(unit_neg)
        rows_d.append(-l_q[j])
        unit_pos = [Fraction(1 if k == j else 0) for k in range(n)]
        rows_c.append(unit_pos)
        rows_d.append(umax_q[j])

    total_rows = len(rows_c)
    if total_rows < n:
        return None

    # Rank rows by floating-point slack |d_i - c_i . u_float|
    ranked = sorted(
        range(total_rows),
        key=lambda i: abs(
            float(rows_d[i])
            - sum(float(rows_c[i][j]) * float(u_float[j]) for j in range(n))
        ),
    )[: min(pool_limit, total_rows)]

    best_u: tuple[Fraction, ...] | None = None
    best_dist: float = float("inf")
    for indices in itertools.combinations(ranked, n):
        sub_c = [rows_c[i] for i in indices]
        sub_d = [rows_d[i] for i in indices]
        u_vert = _solve_exact_linear_system(sub_c, sub_d)
        if u_vert is None:
            continue
        if _primal_margin(a_q, b_q, l_q, umax_q, u_vert) >= 0:
            dist = sum((float(u_vert[j]) - float(u_float[j])) ** 2 for j in range(n))
            if dist < best_dist:
                best_dist = dist
                best_u = u_vert
    return best_u


def _attempt_farkas_repair(
    a_q: list[list[Fraction]],
    b_q: list[Fraction],
    l_q: list[Fraction],
    umax_q: list[Fraction],
    y_float: Sequence[float] | None = None,
    pool_limit: int = 10,
) -> tuple[tuple[Fraction, ...], tuple[Fraction, ...], tuple[Fraction, ...], Fraction] | None:
    """Search for an exact nonnegative Farkas infeasibility certificate in a bounded row pool."""
    m = len(b_q)
    n = len(l_q)
    # Check simple box-vs-box or single-row box infeasibility first:
    for j in range(n):
        if l_q[j] > umax_q[j]:
            y_zero = tuple(Fraction(0) for _ in range(m))
            z_lo = tuple(Fraction(1 if k == j else 0) for k in range(n))
            z_hi = tuple(Fraction(1 if k == j else 0) for k in range(n))
            rhs = umax_q[j] - l_q[j]
            return y_zero, z_lo, z_hi, rhs

    for i in range(m):
        # Minimum possible value of (A_i . u) over box [l, u_max]
        min_au = sum(
            (a_q[i][j] * (l_q[j] if a_q[i][j] >= 0 else umax_q[j]) for j in range(n)),
            Fraction(0),
        )
        if min_au > b_q[i]:
            y_unit = tuple(Fraction(1 if r == i else 0) for r in range(m))
            z_hi = tuple(max(-a_q[i][j], Fraction(0)) for j in range(n))
            z_lo = tuple(max(a_q[i][j], Fraction(0)) for j in range(n))
            rhs = b_q[i] - min_au
            return y_unit, z_lo, z_hi, rhs

    # Combine halfspace rows and box rows into C u <= d, find nonnegative w with C^T w = 0, d^T w = -1
    rows_c: list[list[Fraction]] = list(a_q)
    rows_d: list[Fraction] = list(b_q)
    row_tags: list[tuple[str, int]] = [("A", i) for i in range(m)]
    for j in range(n):
        rows_c.append([Fraction(-1 if k == j else 0) for k in range(n)])
        rows_d.append(-l_q[j])
        row_tags.append(("lo", j))
        rows_c.append([Fraction(1 if k == j else 0) for k in range(n)])
        rows_d.append(umax_q[j])
        row_tags.append(("hi", j))

    total = len(rows_c)
    if total < n + 1:
        return None

    if y_float is not None and len(y_float) == m:
        weights_hint = [abs(float(y_float[i])) for i in range(m)] + [0.1] * (2 * n)
        pool = sorted(range(total), key=lambda idx: -weights_hint[idx])[: min(pool_limit, total)]
    else:
        pool = list(range(min(pool_limit, total)))

    for indices in itertools.combinations(pool, n + 1):
        mat = [[rows_c[i][j] for i in indices] for j in range(n)] + [
            [rows_d[i] for i in indices]
        ]
        rhs_target = [Fraction(0)] * n + [Fraction(-1)]
        w_sol = _solve_exact_linear_system(mat, rhs_target)
        if w_sol is not None and all(w >= 0 for w in w_sol):
            y_out = [Fraction(0)] * m
            z_lo_out = [Fraction(0)] * n
            z_hi_out = [Fraction(0)] * n
            for idx, w_val in zip(indices, w_sol, strict=True):
                kind, k_idx = row_tags[idx]
                if kind == "A":
                    y_out[k_idx] += w_val
                elif kind == "lo":
                    z_lo_out[k_idx] += w_val
                else:
                    z_hi_out[k_idx] += w_val
            # Simplify if both z_lo_out[j] and z_hi_out[j] are positive
            rhs_val = (
                sum((y_out[i] * b_q[i] for i in range(m)), Fraction(0))
                + sum((z_hi_out[j] * umax_q[j] for j in range(n)), Fraction(0))
                - sum((z_lo_out[j] * l_q[j] for j in range(n)), Fraction(0))
            )
            if rhs_val < 0:
                return tuple(y_out), tuple(z_lo_out), tuple(z_hi_out), rhs_val
    return None


@lean_theorem(
    "Research.TransportCertificate",
    (
        "fourSupportLower",
        "fourSupportUpper",
        "four_support_interval_sound",
        "lp_dual_upper_bound",
        "farkas_box_infeasibility_certificate",
    ),
    domain="certified_guard",
    summary=(
        "OSQP/CVXPY exact rational safety-filter certificate verifier and 4-support "
        "correction interval constructor."
    ),
)
def certify_osqp_safety_filter(
    a_mat: Sequence[Sequence[int | float | str | Fraction]],
    b_vec: Sequence[int | float | str | Fraction],
    l_vec: Sequence[int | float | str | Fraction],
    u_max_vec: Sequence[int | float | str | Fraction],
    u_candidate: Sequence[int | float | str | Fraction] | None = None,
    *,
    y_farkas: Sequence[int | float | str | Fraction] | None = None,
    z_lo_farkas: Sequence[int | float | str | Fraction] | None = None,
    z_hi_farkas: Sequence[int | float | str | Fraction] | None = None,
    u_fallback: Sequence[int | float | str | Fraction] | None = None,
    u_nominal: Sequence[int | float | str | Fraction] | None = None,
    support_bounds: tuple[
        int | float | str | Fraction,
        int | float | str | Fraction,
        int | float | str | Fraction,
        int | float | str | Fraction,
    ]
    | None = None,
    alpha: int | float | str | Fraction = Fraction(1, 8),
    beta: int | float | str | Fraction = Fraction(3, 4),
    max_denominator: int = 10000,
    reconstruction_tol: float = 1e-4,
    allow_active_set_repair: bool = True,
    solve_with_osqp: bool = False,
    expected_model_sha256: str | None = None,
) -> CertifiedGuardResult:
    """Certify a candidate safety-filter control ``u`` or Farkas infeasibility witness over Q.

    Returns a ``CertifiedGuardResult`` with ``status`` in:
    - ``"accepted"``: exact rational primal feasibility (and 4-support interval membership when
      ``support_bounds`` is supplied) or exact rational Farkas infeasibility is proved.
    - ``"rejected_certificate"``: model digest mismatch, invalid dimensions/non-finite inputs,
      or a purported candidate/certificate violates constraints beyond numerical reconstruction.
    - ``"inconclusive_reconstruction"``: floating-point solver output was near-feasible (or
      reported infeasibility) within ``reconstruction_tol`` but could not be reconstructed into
      an exact rational witness at ``max_denominator``.
    """
    m = len(b_vec)
    n = len(l_vec)
    fb_default = tuple(Fraction(0) for _ in range(max(n, 1)))
    if (
        m == 0
        or n == 0
        or len(a_mat) != m
        or any(len(row) != n for row in a_mat)
        or len(u_max_vec) != n
    ):
        empty_sha = _canonical_sha256({"error": "invalid_dimensions"})
        return CertifiedGuardResult(
            status="rejected_certificate",
            certificate_type="none",
            u_certified=fb_default,
            u_fallback=fb_default,
            u_output_float=tuple(float(v) for v in fb_default),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=None,
            safe_correction_interval=None,
            model_sha256=empty_sha,
            certificate_sha256=empty_sha,
            reason="invalid_dimensions",
        )

    try:
        a_q = [[_to_fraction(v, max_denominator) for v in row] for row in a_mat]
        b_q = [_to_fraction(v, max_denominator) for v in b_vec]
        l_q = [_to_fraction(v, max_denominator) for v in l_vec]
        umax_q = [_to_fraction(v, max_denominator) for v in u_max_vec]
        fb_q = (
            tuple(_to_fraction(v, max_denominator) for v in u_fallback)
            if u_fallback is not None
            else tuple(Fraction(0) for _ in range(n))
        )
        if len(fb_q) != n:
            raise ValueError("u_fallback length mismatch.")
        alpha_q = _to_fraction(alpha, max_denominator)
        beta_q = _to_fraction(beta, max_denominator)
        supp_q: tuple[Fraction, Fraction, Fraction, Fraction] | None = None
        corr_interval: tuple[Fraction, Fraction] | None = None
        if support_bounds is not None:
            if len(support_bounds) != 4:
                raise ValueError("support_bounds must have 4 elements (wl, wu, bl, bu).")
            supp_q = (
                _to_fraction(support_bounds[0], max_denominator),
                _to_fraction(support_bounds[1], max_denominator),
                _to_fraction(support_bounds[2], max_denominator),
                _to_fraction(support_bounds[3], max_denominator),
            )
            iv_info = compute_four_support_interval(
                supp_q[0], supp_q[1], supp_q[2], supp_q[3], alpha_q, beta_q
            )
            if iv_info["nonempty"]:
                corr_interval = (iv_info["u_min"], iv_info["u_max"])
    except ValueError as exc:
        err_sha = _canonical_sha256({"error": str(exc)})
        return CertifiedGuardResult(
            status="rejected_certificate",
            certificate_type="none",
            u_certified=fb_default,
            u_fallback=fb_default,
            u_output_float=tuple(float(v) for v in fb_default),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=None,
            safe_correction_interval=None,
            model_sha256=err_sha,
            certificate_sha256=err_sha,
            reason=f"invalid_input: {exc}",
        )

    model_payload = {
        "A": [[str(v) for v in row] for row in a_q],
        "b": [str(v) for v in b_q],
        "l": [str(v) for v in l_q],
        "u_max": [str(v) for v in umax_q],
        "support_bounds": [str(v) for v in supp_q] if supp_q is not None else None,
        "alpha": str(alpha_q),
        "beta": str(beta_q),
    }
    model_sha = _canonical_sha256(model_payload)

    if expected_model_sha256 is not None and expected_model_sha256 != model_sha:
        cert_sha = _canonical_sha256(
            {"model_sha256": model_sha, "status": "rejected_certificate", "reason": "model_sha256_mismatch"}
        )
        return CertifiedGuardResult(
            status="rejected_certificate",
            certificate_type="none",
            u_certified=fb_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in fb_q),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason="model_sha256_mismatch",
        )

    # Optionally invoke OSQP when requested
    osqp_status: str | None = None
    if solve_with_osqp and u_candidate is None and y_farkas is None:
        import osqp
        from scipy import sparse

        u_nom_f = (
            np.array([float(_to_fraction(v, max_denominator)) for v in u_nominal], dtype=float)
            if u_nominal is not None
            else np.zeros(n, dtype=float)
        )
        a_np = np.vstack([
            np.array([[float(v) for v in row] for row in a_q], dtype=float),
            np.eye(n, dtype=float),
        ])
        l_np = np.concatenate([
            np.full(m, -np.inf, dtype=float),
            np.array([float(v) for v in l_q], dtype=float),
        ])
        u_np = np.concatenate([
            np.array([float(v) for v in b_q], dtype=float),
            np.array([float(v) for v in umax_q], dtype=float),
        ])
        solver = osqp.OSQP()
        solver.setup(
            P=sparse.eye(n, format="csc", dtype=float),
            q=-u_nom_f,
            A=sparse.csc_matrix(a_np),
            l=l_np,
            u=u_np,
            verbose=False,
            polishing=True,
            eps_abs=1e-9,
            eps_rel=1e-9,
        )
        res = solver.solve(raise_error=False)
        osqp_status = res.info.status
        if osqp_status == "solved" and res.x is not None:
            u_candidate = [float(v) for v in res.x]
        elif "infeasible" in osqp_status and res.prim_inf_cert is not None:
            cert_vec = [float(v) for v in res.prim_inf_cert]
            y_farkas = [max(cert_vec[i], 0.0) for i in range(m)]
            z_hi_farkas = [max(cert_vec[m + j], 0.0) for j in range(n)]
            z_lo_farkas = [max(-cert_vec[m + j], 0.0) for j in range(n)]
        else:
            cert_sha = _canonical_sha256(
                {"model_sha256": model_sha, "osqp_status": osqp_status}
            )
            return CertifiedGuardResult(
                status="inconclusive_reconstruction",
                certificate_type="none",
                u_certified=fb_q,
                u_fallback=fb_q,
                u_output_float=tuple(float(v) for v in fb_q),
                primal_residual_margin=Fraction(-1),
                farkas_stationarity_residual=Fraction(0),
                farkas_rhs_margin=Fraction(0),
                support_bounds=supp_q,
                safe_correction_interval=corr_interval,
                model_sha256=model_sha,
                certificate_sha256=cert_sha,
                reason=f"inconclusive_osqp_status:{osqp_status}",
            )

    # Branch 1: Check / reconstruct Farkas infeasibility certificate if provided
    if y_farkas is not None:
        if len(y_farkas) != m:
            cert_sha = _canonical_sha256({"model_sha256": model_sha, "error": "y_farkas_len"})
            return CertifiedGuardResult(
                status="rejected_certificate",
                certificate_type="none",
                u_certified=fb_q,
                u_fallback=fb_q,
                u_output_float=tuple(float(v) for v in fb_q),
                primal_residual_margin=Fraction(-1),
                farkas_stationarity_residual=Fraction(0),
                farkas_rhs_margin=Fraction(0),
                support_bounds=supp_q,
                safe_correction_interval=corr_interval,
                model_sha256=model_sha,
                certificate_sha256=cert_sha,
                reason="y_farkas_length_mismatch",
            )
        is_float_farkas = any(isinstance(v, (float, np.floating)) for v in y_farkas)
        try:
            farkas_check = verify_farkas_box_certificate(
                a_q,
                b_q,
                l_q,
                umax_q,
                y_farkas,
                z_lo_farkas,
                z_hi_farkas,
                max_denominator=max_denominator,
            )
        except ValueError as exc:
            cert_sha = _canonical_sha256({"model_sha256": model_sha, "error": str(exc)})
            return CertifiedGuardResult(
                status="rejected_certificate",
                certificate_type="none",
                u_certified=fb_q,
                u_fallback=fb_q,
                u_output_float=tuple(float(v) for v in fb_q),
                primal_residual_margin=Fraction(-1),
                farkas_stationarity_residual=Fraction(0),
                farkas_rhs_margin=Fraction(0),
                support_bounds=supp_q,
                safe_correction_interval=corr_interval,
                model_sha256=model_sha,
                certificate_sha256=cert_sha,
                reason=f"invalid_farkas_certificate:{exc}",
            )

        if farkas_check["valid"]:
            cert_sha = _canonical_sha256(
                {
                    "model_sha256": model_sha,
                    "certificate_type": "farkas_infeasible",
                    "y": [str(v) for v in farkas_check["y_q"]],
                    "z_lo": [str(v) for v in farkas_check["z_lo_q"]],
                    "z_hi": [str(v) for v in farkas_check["z_hi_q"]],
                    "farkas_rhs": str(farkas_check["farkas_rhs"]),
                }
            )
            return CertifiedGuardResult(
                status="accepted",
                certificate_type="farkas_infeasible",
                u_certified=fb_q,
                u_fallback=fb_q,
                u_output_float=tuple(float(v) for v in fb_q),
                primal_residual_margin=Fraction(0),
                farkas_stationarity_residual=farkas_check["stationarity_residual"],
                farkas_rhs_margin=farkas_check["farkas_rhs"],
                support_bounds=supp_q,
                safe_correction_interval=corr_interval,
                model_sha256=model_sha,
                certificate_sha256=cert_sha,
                reason="accepted_exact_farkas_infeasibility_certificate",
            )

        # If float Farkas certificate did not round cleanly, try exact basis repair if allowed
        if is_float_farkas and allow_active_set_repair:
            repaired_farkas = _attempt_farkas_repair(
                a_q, b_q, l_q, umax_q, [float(v) for v in y_farkas]
            )
            if repaired_farkas is not None:
                y_rep, zlo_rep, zhi_rep, rhs_rep = repaired_farkas
                cert_sha = _canonical_sha256(
                    {
                        "model_sha256": model_sha,
                        "certificate_type": "farkas_infeasible",
                        "y": [str(v) for v in y_rep],
                        "z_lo": [str(v) for v in zlo_rep],
                        "z_hi": [str(v) for v in zhi_rep],
                        "farkas_rhs": str(rhs_rep),
                    }
                )
                return CertifiedGuardResult(
                    status="accepted",
                    certificate_type="farkas_infeasible",
                    u_certified=fb_q,
                    u_fallback=fb_q,
                    u_output_float=tuple(float(v) for v in fb_q),
                    primal_residual_margin=Fraction(0),
                    farkas_stationarity_residual=Fraction(0),
                    farkas_rhs_margin=rhs_rep,
                    support_bounds=supp_q,
                    safe_correction_interval=corr_interval,
                    model_sha256=model_sha,
                    certificate_sha256=cert_sha,
                    reason="accepted_repaired_exact_farkas_certificate",
                )

        # Distinguish inconclusive float rounding from forged/invalid certificate
        near_farkas = (
            is_float_farkas
            and farkas_check["nonneg_ok"]
            and float(farkas_check["stationarity_residual"]) <= reconstruction_tol
            and float(farkas_check["farkas_rhs"]) < reconstruction_tol
        )
        status_out: CertifiedGuardStatus = (
            "inconclusive_reconstruction" if near_farkas else "rejected_certificate"
        )
        cert_sha = _canonical_sha256(
            {
                "model_sha256": model_sha,
                "status": status_out,
                "stationarity_residual": str(farkas_check["stationarity_residual"]),
                "farkas_rhs": str(farkas_check["farkas_rhs"]),
            }
        )
        return CertifiedGuardResult(
            status=status_out,
            certificate_type="none",
            u_certified=fb_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in fb_q),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=farkas_check["stationarity_residual"],
            farkas_rhs_margin=farkas_check["farkas_rhs"],
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason=(
                "inconclusive_farkas_rational_reconstruction"
                if near_farkas
                else "rejected_invalid_farkas_certificate"
            ),
        )

    # Branch 2: Check / reconstruct primal candidate u_candidate
    if u_candidate is None:
        cert_sha = _canonical_sha256({"model_sha256": model_sha, "error": "missing_candidate"})
        return CertifiedGuardResult(
            status="rejected_certificate",
            certificate_type="none",
            u_certified=fb_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in fb_q),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason="missing_candidate_and_certificate",
        )

    if len(u_candidate) != n:
        cert_sha = _canonical_sha256({"model_sha256": model_sha, "error": "u_candidate_len"})
        return CertifiedGuardResult(
            status="rejected_certificate",
            certificate_type="none",
            u_certified=fb_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in fb_q),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason="u_candidate_length_mismatch",
        )

    is_float_cand = any(isinstance(v, (float, np.floating)) for v in u_candidate)
    try:
        u_q = tuple(_to_fraction(v, max_denominator) for v in u_candidate)
    except ValueError as exc:
        cert_sha = _canonical_sha256({"model_sha256": model_sha, "error": str(exc)})
        return CertifiedGuardResult(
            status="rejected_certificate",
            certificate_type="none",
            u_certified=fb_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in fb_q),
            primal_residual_margin=Fraction(-1),
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason=f"invalid_u_candidate:{exc}",
        )

    # Effective box bounds incorporate 4-support interval on u[0] when support_bounds is given
    eff_l_q = list(l_q)
    eff_umax_q = list(umax_q)
    if supp_q is not None:
        if corr_interval is None:
            cert_sha = _canonical_sha256(
                {"model_sha256": model_sha, "error": "empty_four_support_interval"}
            )
            return CertifiedGuardResult(
                status="rejected_certificate",
                certificate_type="none",
                u_certified=fb_q,
                u_fallback=fb_q,
                u_output_float=tuple(float(v) for v in fb_q),
                primal_residual_margin=Fraction(-1),
                farkas_stationarity_residual=Fraction(0),
                farkas_rhs_margin=Fraction(0),
                support_bounds=supp_q,
                safe_correction_interval=None,
                model_sha256=model_sha,
                certificate_sha256=cert_sha,
                reason="empty_four_support_interval",
            )
        eff_l_q[0] = max(eff_l_q[0], corr_interval[0])
        eff_umax_q[0] = min(eff_umax_q[0], corr_interval[1])

    margin = _primal_margin(a_q, b_q, eff_l_q, eff_umax_q, u_q)
    if margin >= 0:
        cert_type = (
            "four_support_interval" if supp_q is not None else "primal_feasible"
        )
        cert_sha = _canonical_sha256(
            {
                "model_sha256": model_sha,
                "certificate_type": cert_type,
                "u_certified": [str(v) for v in u_q],
                "primal_residual_margin": str(margin),
            }
        )
        return CertifiedGuardResult(
            status="accepted",
            certificate_type=cert_type,
            u_certified=u_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in u_q),
            primal_residual_margin=margin,
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason="accepted_exact_primal_certificate",
        )

    # If float candidate slightly violated a tight active constraint due to float/rounding,
    # try exact active-set vertex repair if enabled
    if is_float_cand and float(margin) >= -reconstruction_tol:
        if allow_active_set_repair:
            u_rep = _attempt_active_set_primal_repair(
                a_q, b_q, eff_l_q, eff_umax_q, [float(v) for v in u_candidate]
            )
            if u_rep is not None:
                rep_margin = _primal_margin(a_q, b_q, eff_l_q, eff_umax_q, u_rep)
                cert_type = (
                    "four_support_interval" if supp_q is not None else "primal_feasible"
                )
                cert_sha = _canonical_sha256(
                    {
                        "model_sha256": model_sha,
                        "certificate_type": cert_type,
                        "u_certified": [str(v) for v in u_rep],
                        "primal_residual_margin": str(rep_margin),
                    }
                )
                return CertifiedGuardResult(
                    status="accepted",
                    certificate_type=cert_type,
                    u_certified=u_rep,
                    u_fallback=fb_q,
                    u_output_float=tuple(float(v) for v in u_rep),
                    primal_residual_margin=rep_margin,
                    farkas_stationarity_residual=Fraction(0),
                    farkas_rhs_margin=Fraction(0),
                    support_bounds=supp_q,
                    safe_correction_interval=corr_interval,
                    model_sha256=model_sha,
                    certificate_sha256=cert_sha,
                    reason="accepted_repaired_active_set_primal_certificate",
                )

        cert_sha = _canonical_sha256(
            {
                "model_sha256": model_sha,
                "status": "inconclusive_reconstruction",
                "primal_residual_margin": str(margin),
            }
        )
        return CertifiedGuardResult(
            status="inconclusive_reconstruction",
            certificate_type="none",
            u_certified=fb_q,
            u_fallback=fb_q,
            u_output_float=tuple(float(v) for v in fb_q),
            primal_residual_margin=margin,
            farkas_stationarity_residual=Fraction(0),
            farkas_rhs_margin=Fraction(0),
            support_bounds=supp_q,
            safe_correction_interval=corr_interval,
            model_sha256=model_sha,
            certificate_sha256=cert_sha,
            reason="inconclusive_primal_rational_reconstruction",
        )

    cert_sha = _canonical_sha256(
        {
            "model_sha256": model_sha,
            "status": "rejected_certificate",
            "primal_residual_margin": str(margin),
        }
    )
    return CertifiedGuardResult(
        status="rejected_certificate",
        certificate_type="none",
        u_certified=fb_q,
        u_fallback=fb_q,
        u_output_float=tuple(float(v) for v in fb_q),
        primal_residual_margin=margin,
        farkas_stationarity_residual=Fraction(0),
        farkas_rhs_margin=Fraction(0),
        support_bounds=supp_q,
        safe_correction_interval=corr_interval,
        model_sha256=model_sha,
        certificate_sha256=cert_sha,
        reason="rejected_primal_constraint_violation",
    )


@lean_theorem(
    "Research.TransportCertificate",
    ("fourSupportLower", "fourSupportUpper", "four_support_interval_sound"),
    domain="certified_guard",
    summary=(
        "Idempotent PLC command-admission box guard matching C99 ctrl_certified_box_guard "
        "and IEC 61131-3 FB_CtrlCertifiedGuard."
    ),
)
def certified_plc_box_guard(
    receipt_verified: bool,
    snapshot_coherent: bool,
    certified_version: int,
    current_version: int,
    wl: T,
    wu: T,
    bl: T,
    bu: T,
    alpha: T,
    beta: T,
    base_setpoint: T,
    u_cmd: T,
    u_fallback: T,
) -> dict[str, T | bool]:
    """Evaluate the idempotent static PLC command guard over float or exact Fraction.

    Computes the 4-support interval ``[u_min, u_max]`` and outputs the absolute setpoint
    ``base_setpoint + u_cmd`` if all admission gates pass, or ``base_setpoint + u_fallback``
    otherwise. Repeated evaluations on the same snapshot are strictly idempotent.
    """
    u_min: T = max(-alpha - wl, -beta - bl)
    u_max: T = min(alpha - wu, beta - bu)
    admitted = bool(
        receipt_verified
        and snapshot_coherent
        and (certified_version == current_version)
        and (alpha <= beta)
        and (wl <= wu)
        and (bl <= bu)
        and (u_min <= u_max)
        and (u_min <= u_cmd <= u_max)
    )
    setpoint_out: T = (base_setpoint + u_cmd) if admitted else (base_setpoint + u_fallback)
    return {
        "accepted": admitted,
        "u_min": u_min,
        "u_max": u_max,
        "setpoint_out": setpoint_out,
    }
