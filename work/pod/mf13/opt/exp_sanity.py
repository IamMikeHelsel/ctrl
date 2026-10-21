"""Sanity checks and the n=7 deflation diagnostic. No search yet."""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from numpy.linalg import norm, svd

import lyap as L

OUT = Path(__file__).resolve().parent / "results"
OUT.mkdir(exist_ok=True)


def check_gradient(rng):
    errs = []
    for n, sym in ((6, True), (6, False), (7, True), (7, False)):
        A = rng.normal(size=(n, n))
        basis = L.SYM[n] if sym else L.SKEW[n]
        val, g = L.norm_grad_A(A, sym)
        direction = rng.normal(size=(n, n))
        eps = 1e-6
        vp, _ = L.norm_grad_A(A + eps * direction, sym)
        vm, _ = L.norm_grad_A(A - eps * direction, sym)
        errs.append(abs((vp - vm) / (2 * eps) - np.sum(g * direction)))
        B = L.op_matrix(A, basis)
        assert abs(svd(B, compute_uv=False)[0] - val) < 1e-12
    return float(max(errs))


def check_system_roundtrip(rng):
    A = rng.normal(size=(6, 6))
    basis = L.SKEW[6]
    u, sv, vt = svd(L.op_matrix(A, basis), full_matrices=False)
    # Use a middle singular component so K is less likely to be tiny.
    i = int(np.argmax([svd(np.einsum("a,aij->ij", vt[j], basis), compute_uv=False)[-1] for j in range(len(sv))]))
    K = np.einsum("a,aij->ij", vt[i], basis)
    Y = np.einsum("a,aij->ij", u[:, i], basis) * sv[i]
    # Equations for unscaled A: L(K)=sig Y_unit, L*(Y_unit)=sig K.
    # coupled_system expects L(K)=Y and L*(Y)=K, so pass Y_scaled = sig * Y_unit
    # and right hand K_scaled = sig * K, OR scale A.
    As = A / sv[i]
    Yu = np.einsum("a,aij->ij", u[:, i], basis)
    C, rhs = L.coupled_system(K, Yu)
    got = C @ As.reshape(-1)
    resid = float(norm(got - rhs))
    fam = L.factor_family(K, Yu)
    # As itself should be a particular solution of a consistent system.
    return {
        "roundtrip_resid": resid,
        "consistent": fam["consistent"],
        "rank": fam["rank"],
        "nullity": fam["nullity"],
        "elimination_resid": fam["residual"],
        "witness_smin": float(svd(K, compute_uv=False)[-1]),
        "sigma": float(sv[i]),
    }


def check_inner_gradient(rng):
    K = L.canon([1.0, 2.0, 3.0])
    K = K / norm(K)
    Y = K.copy()
    fam = L.factor_family(K, Y)
    z = rng.normal(size=fam["nullity"])
    val, jac = L.family_objective(fam, z, "s")
    direction = rng.normal(size=fam["nullity"])
    eps = 1e-6
    vp, _ = L.family_objective(fam, z + eps * direction, "s")
    vm, _ = L.family_objective(fam, z - eps * direction, "s")
    return {
        "nullity": fam["nullity"],
        "rank": fam["rank"],
        "consistent": fam["consistent"],
        "grad_err": float(abs((vp - vm) / (2 * eps) - np.dot(jac, direction))),
    }


def calibration():
    K = L.canon([1.0, 2.0, 3.0])
    fam = L.factor_family(K, K)
    opt = L.minimize_symmetric(fam, starts=3, rng=np.random.default_rng(1))
    cert, spectrum, active = L.subdifferential_certificate(fam, opt["z"], gap_tol=1e-7)
    s, k = L.restricted_norms(opt["A"])
    # A = I/2 should be feasible and have s=k=1.
    A = 0.5 * np.eye(6)
    s0, k0 = L.restricted_norms(A)
    r1 = norm(A @ K + K @ A.T - K)
    r2 = norm(A.T @ K + K @ A - K)
    return {
        "rank": fam["rank"],
        "nullity": fam["nullity"],
        "consistent": fam["consistent"],
        "phi": opt["phi"] if "phi" in opt else opt["s"],
        "s_at_opt": s,
        "k_at_opt": k,
        "cert_subgrad": cert,
        "active": int(len(active)),
        "s_half": s0,
        "k_half": k0,
        "half_equation_resid": float(np.sqrt(r1**2 + r2**2)),
        "opt_grad_norm": opt["grad_norm"],
    }


def equal_weight_family(rng):
    K = L.canon([1.0, 1.0, 1.0])
    K = K / norm(K)
    fam = L.factor_family(K, K)
    # Sample the affine family. Hull of the minimum should sit at 1.
    samples = []
    for _ in range(40):
        z = rng.normal(size=fam["nullity"])
        A = (fam["a_part"] + fam["null"] @ z).reshape(6, 6)
        s, k = L.restricted_norms(A)
        samples.append((s, k, k - s))
    opt = L.minimize_symmetric(fam, starts=3, rng=rng)
    s, k = L.restricted_norms(opt["A"])
    arr = np.array(samples)
    return {
        "rank": fam["rank"],
        "nullity": fam["nullity"],
        "residual": fam["residual"],
        "phi": s,
        "k_at_phi": k,
        "gap_at_phi": k - s,
        "sample_min_s": float(arr[:, 0].min()),
        "sample_max_gap": float(arr[:, 2].max()),
        "sample_min_gap": float(arr[:, 2].min()),
        "cert": L.subdifferential_certificate(fam, opt["z"])[0],
    }


def n7_diagnostics():
    s, k = L.restricted_norms(L.A7)
    spec_s, spec_k = L.restricted_spectrum(L.A7)
    image = L.A7 @ L.K7 + L.K7 @ L.A7.T
    rayleigh = float(norm(image) / norm(L.K7))
    sk = svd(L.K7, compute_uv=False)
    # Kernel of K7 (odd dimension, at least one).
    u, sv, vt = svd(L.K7)
    ker = vt[-1]
    # Principal submatrices.
    principals = []
    for drop in range(7):
        idx = [i for i in range(7) if i != drop]
        A = L.A7[np.ix_(idx, idx)]
        ss, kk = L.restricted_norms(A)
        principals.append(
            {
                "drop": drop,
                "s": ss,
                "k": kk,
                "gap": kk - ss,
                "rel_gap": L.relative_gap(kk, ss),
                "spectral_norm": float(svd(A, compute_uv=False)[0]),
            }
        )
    # Row-scaling homotopy on the last row (last column of A7 is already zero).
    homotopy = []
    for t in np.linspace(1.0, 0.0, 11):
        A = L.A7.copy()
        A[6, :] *= t
        ss, kk = L.restricted_norms(A)
        homotopy.append({"t": float(t), "s": ss, "k": kk, "gap": kk - ss, "rel": L.relative_gap(kk, ss)})
    # Two-sided scaling of each coordinate: row and column multiplied by t.
    death = []
    for drop in range(7):
        path = []
        for t in (1.0, 0.5, 0.25, 0.1, 0.0):
            M = np.eye(7)
            M[drop, drop] = t
            A = M @ L.A7 @ M
            ss, kk = L.restricted_norms(A)
            path.append({"t": t, "gap": kk - ss, "rel": L.relative_gap(kk, ss), "s": ss, "k": kk})
        death.append({"drop": drop, "path": path})
    return {
        "s": s,
        "k": k,
        "gap": k - s,
        "rel_gap": L.relative_gap(k, s),
        "s_squared": s**2,
        "k_squared": k**2,
        "paper_s_squared": 1195.593985,
        "paper_k_squared": 1196.025224,
        "K7_singular_values": sk.tolist(),
        "K7_rayleigh": rayleigh,
        "K7_kernel": ker.tolist(),
        "image_over_K_squared_ratio": float(norm(image) ** 2 / norm(L.K7) ** 2),
        "principals": principals,
        "last_row_homotopy": homotopy,
        "two_sided_death": death,
        "spec_s_top5": spec_s[:5].tolist(),
        "spec_k_top5": spec_k[:5].tolist(),
    }


def compression_scan(rng):
    """Best gap of a 6x6 compression of the fixed 7x7 counterexample.

    Grassmannian Gr(6,7) is 6-dimensional. Multistart Riemannian-ish
    projected gradient on the Stiefel manifold.
    """
    A = L.A7
    best = None
    history = []

    def gap_of(Q):
        M = Q.T @ A @ Q
        s, k = L.restricted_norms(M)
        return k - s, s, k, M

    def grad_Q(Q):
        # Central differences on ambient 7x6, then project to the Stiefel tangent.
        eps = 1e-6
        g = np.zeros_like(Q)
        base, _, _, _ = gap_of(Q)
        for i in range(Q.shape[0]):
            for j in range(Q.shape[1]):
                Q[i, j] += eps
                gp, _, _, _ = gap_of(Q)
                Q[i, j] -= 2 * eps
                gm, _, _, _ = gap_of(Q)
                Q[i, j] += eps
                g[i, j] = (gp - gm) / (2 * eps)
        # Tangent projection: G <- G - Q sym(Q^T G)
        G = g - Q @ ((Q.T @ g + (Q.T @ g).T) / 2.0)
        return G, base

    starts = []
    # Coordinate deletions.
    for drop in range(7):
        idx = [i for i in range(7) if i != drop]
        Q = np.eye(7)[:, idx]
        starts.append(Q)
    # Kernel-orthogonal compression.
    ker = svd(L.K7)[2][-1]
    # Orthonormal basis of ker^perp via QR of a completion.
    M = np.eye(7)
    M[:, 0] = ker
    Qfull, _ = np.linalg.qr(M)
    # First column aligns with ker only if we use a reflector; rebuild properly.
    P = np.eye(7) - np.outer(ker, ker)
    _, qq = np.linalg.eigh(P)
    Q = qq[:, 1:]  # eigenvalue 1 has multiplicity 6
    if Q.shape[1] != 6:
        Q = qq[:, qq.shape[1] - 6 :]
    starts.append(Q)
    for _ in range(12):
        X = rng.normal(size=(7, 6))
        Q, _ = np.linalg.qr(X)
        starts.append(Q)

    for si, Q in enumerate(starts):
        step = 0.05
        last = None
        for it in range(80):
            G, val = grad_Q(Q)
            gnorm = float(norm(G))
            if last is not None and val < last:
                step *= 0.5
            Q = Q + step * G
            Q, _ = np.linalg.qr(Q)
            last = val
            if gnorm < 1e-7:
                break
        gap, s, k, M = gap_of(Q)
        rec = {"start": si, "gap": gap, "s": s, "k": k, "iters": it, "rel": L.relative_gap(k, s)}
        history.append(rec)
        if best is None or gap > best["gap"]:
            best = {**rec, "A": M, "Q": Q}
    return history, best


def witness_conditioning_survey(rng, trials=30):
    """How full-rank are skew singular vectors of random 6x6 matrices?"""
    rows = []
    for _ in range(trials):
        A = rng.normal(size=(6, 6))
        s_op, k_op = L.restricted_norms(A)
        u, sv, vt = svd(L.op_matrix(A, L.SKEW[6]), full_matrices=False)
        smins = []
        for i in (0, 4, 8, 14):
            K = np.einsum("a,aij->ij", vt[i], L.SKEW[6])
            smins.append(float(svd(K, compute_uv=False)[-1]))
        rows.append(
            {
                "rel_gap": L.relative_gap(k_op, s_op),
                "gap": k_op - s_op,
                "smin_top": smins[0],
                "smin_mid": smins[1],
                "smin_lower": smins[2],
                "smin_smallest_mode": smins[3],
                "sv_skew_top3": sv[:3].tolist(),
            }
        )
    sm = np.array([r["smin_top"] for r in rows])
    gaps = np.array([r["gap"] for r in rows])
    return {
        "trials": trials,
        "top_witness_smin_median": float(np.median(sm)),
        "top_witness_smin_max": float(sm.max()),
        "top_witness_smin_min": float(sm.min()),
        "gap_max": float(gaps.max()),
        "gap_median": float(np.median(gaps)),
        "fraction_top_smin_gt_0.05": float(np.mean(sm > 0.05)),
        "samples": rows[:8],
    }


def main():
    rng = np.random.default_rng(20261018)
    report = {}
    print("gradient", flush=True)
    report["grad_fd_max_err"] = check_gradient(rng)
    print("roundtrip", flush=True)
    report["roundtrip"] = check_system_roundtrip(rng)
    print("inner grad", flush=True)
    report["inner_grad"] = check_inner_gradient(rng)
    print("calibration", flush=True)
    report["calibration"] = calibration()
    print("equal weight", flush=True)
    report["equal_weight"] = equal_weight_family(rng)
    print("n7", flush=True)
    report["n7"] = n7_diagnostics()
    print("conditioning survey", flush=True)
    report["conditioning"] = witness_conditioning_survey(rng)
    print("compression", flush=True)
    hist, best = compression_scan(rng)
    np.save(OUT / "best_compression_A.npy", best["A"])
    np.save(OUT / "best_compression_Q.npy", best["Q"])
    report["compression_best"] = {k: best[k] for k in ("gap", "s", "k", "rel", "start", "iters")}
    report["compression_gap_max"] = max(h["gap"] for h in hist)
    report["compression_gaps"] = [h["gap"] for h in hist]
    # JSON cannot hold numpy types blindly; default=str is too lossy. Convert.
    def conv(o):
        if isinstance(o, np.ndarray):
            return o.tolist()
        if isinstance(o, (np.floating,)):
            return float(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, dict):
            return {k: conv(v) for k, v in o.items()}
        if isinstance(o, (list, tuple)):
            return [conv(v) for v in o]
        return o

    path = OUT / "sanity.json"
    path.write_text(json.dumps(conv(report), indent=2))
    print(json.dumps(conv({k: report[k] for k in report if k != "n7"}), indent=2))
    print("--- n7 principals ---")
    print(json.dumps(conv(report["n7"]["principals"]), indent=2))
    print("--- homotopy ---")
    print(json.dumps(conv(report["n7"]["last_row_homotopy"]), indent=2))
    print("s^2", report["n7"]["s_squared"], "k^2", report["n7"]["k_squared"])


if __name__ == "__main__":
    main()
