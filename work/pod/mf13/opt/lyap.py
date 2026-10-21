"""Numerics for the Byers–Nash / symmetric-maximizer question in dimension 6.

L_A(X) = A X + X A^T.
s(A) is the Frobenius-induced norm of L_A on symmetric matrices.
k(A) is the same norm on skew-symmetric matrices.
A counterexample is a matrix with k(A) > s(A).

For an invertible coupled skew pair normalized so that
    A K + K A^T = Y,    A^T Y + Y A = K,
the value 1 is a skew singular value, hence k(A) >= 1. If some such A
has s(A) < 1, it is a strict counterexample. Rank-at-most-4 witnesses are
excluded by the same-square argument in the research notes; both K and Y
must be invertible.

The linear map on symmetric H,
    (K Y) H - H (Y K) = K^3 - (Y^2 K + K Y^2)/2,
has numerical rank 12 (nullity 9) for generic invertible pairs, and the
right-hand side lies in the image precisely on a codimension-3 variety.
Three trace-moment conditions
    tr((Y K)^j (Y^2 - K^2)) = 0, j = 0,1,2,
cut that variety out in every trial where a Newton retraction succeeded.
"""
from __future__ import annotations

import numpy as np
from numpy.linalg import norm, svd, inv, lstsq
from scipy.optimize import minimize as scipy_minimize

N = 6
J2 = np.array([[0.0, 1.0], [-1.0, 0.0]])


def _basis(n: int, symmetric: bool) -> np.ndarray:
    blocks = []
    if symmetric:
        for i in range(n):
            e = np.zeros((n, n))
            e[i, i] = 1.0
            blocks.append(e)
    for i in range(n):
        for j in range(i + 1, n):
            e = np.zeros((n, n))
            e[i, j] = 1.0 / np.sqrt(2.0)
            e[j, i] = (1.0 if symmetric else -1.0) / np.sqrt(2.0)
            blocks.append(e)
    return np.stack(blocks)


SYM = {n: _basis(n, True) for n in (6, 7)}
SKEW = {n: _basis(n, False) for n in (6, 7)}

_PAIRS = [(i, j) for i in range(N) for j in range(i + 1, N)]


def canon(weights: np.ndarray) -> np.ndarray:
    """Block-diagonal skew matrix diag(w0 J, w1 J, w2 J)."""
    K = np.zeros((N, N))
    for t, w in enumerate(np.asarray(weights, dtype=float)):
        K[2 * t : 2 * t + 2, 2 * t : 2 * t + 2] = float(w) * J2
    return K


def skew_from_coords(y: np.ndarray, n: int = N) -> np.ndarray:
    return np.einsum("a,aij->ij", np.asarray(y, dtype=float), SKEW[n])


def sym_from_coords(h: np.ndarray, n: int = N) -> np.ndarray:
    return np.einsum("a,aij->ij", np.asarray(h, dtype=float), SYM[n])


def skew_coords(K: np.ndarray) -> np.ndarray:
    n = K.shape[0]
    return np.einsum("aij,ij->a", SKEW[n], K)


def sym_coords(H: np.ndarray) -> np.ndarray:
    n = H.shape[0]
    return np.einsum("aij,ij->a", SYM[n], H)


def upper_of(M: np.ndarray) -> np.ndarray:
    return np.array([M[i, j] for i, j in _PAIRS], dtype=float)


def op_matrix(A: np.ndarray, basis: np.ndarray) -> np.ndarray:
    images = np.einsum("ij,mjk->mik", A, basis, optimize=True)
    images = images + np.einsum("mij,jk->mik", basis, A.T, optimize=True)
    return np.einsum("mij,kij->mk", basis, images, optimize=True)


def restricted_norms(A: np.ndarray) -> tuple[float, float]:
    n = A.shape[0]
    s = svd(op_matrix(A, SYM[n]), compute_uv=False)[0]
    k = svd(op_matrix(A, SKEW[n]), compute_uv=False)[0]
    return float(s), float(k)


def restricted_spectrum(A: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    n = A.shape[0]
    s = svd(op_matrix(A, SYM[n]), compute_uv=False)
    k = svd(op_matrix(A, SKEW[n]), compute_uv=False)
    return s, k


def top_singular_pair(A: np.ndarray, symmetric: bool) -> tuple[float, np.ndarray, np.ndarray]:
    """Largest singular value and its right/left matrix witnesses."""
    n = A.shape[0]
    basis = SYM[n] if symmetric else SKEW[n]
    u, sv, vt = svd(op_matrix(A, basis), full_matrices=False)
    right = np.einsum("a,aij->ij", vt[0], basis)
    left = np.einsum("a,aij->ij", u[:, 0], basis)
    return float(sv[0]), right, left


def norm_grad_A(A: np.ndarray, symmetric: bool) -> tuple[float, np.ndarray]:
    """Operator norm and Euclidean gradient with respect to A.

    If the top singular value is multiple this is one subgradient.
    """
    n = A.shape[0]
    basis = SYM[n] if symmetric else SKEW[n]
    u, sv, vt = svd(op_matrix(A, basis), full_matrices=False)
    right = np.einsum("a,aij->ij", vt[0], basis)
    left = np.einsum("a,aij->ij", u[:, 0], basis)
    grad = left @ right.T + left.T @ right
    return float(sv[0]), grad


def moments(K: np.ndarray, Y: np.ndarray, count: int = 3) -> np.ndarray:
    G = Y @ K
    D = Y @ Y - K @ K
    P = np.eye(K.shape[0])
    out = np.empty(count)
    for j in range(count):
        out[j] = np.trace(P @ D)
        P = P @ G
    return out


def coupled_system(K: np.ndarray, Y: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """30 x 36 matrix of the two coupled Lyapunov equations in vec(A).

    Row-major vectorization. Upper-triangular coordinates of
        A K + K A^T = Y,    A^T Y + Y A = K.
    """
    n = N
    C = np.zeros((30, n * n))
    for col, (p, q) in enumerate(((p, q) for p in range(n) for q in range(n))):
        # A = E_{pq}
        EK = np.zeros((n, n))
        EK[p, :] = K[q, :]
        KET = np.zeros((n, n))
        KET[:, p] = K[:, q]
        M1 = EK + KET
        # A^T Y + Y A
        AT = np.zeros((n, n))
        AT[q, :] = Y[p, :]
        YA = np.zeros((n, n))
        YA[:, q] = Y[:, p]
        M2 = AT + YA
        C[:15, col] = upper_of(M1)
        C[15:, col] = upper_of(M2)
    rhs = np.concatenate([upper_of(Y), upper_of(K)])
    return C, rhs


def factor_family(K: np.ndarray, Y: np.ndarray, rank_tol: float = 1e-9):
    """Affine data for A such that the coupled equations hold.

    Returns a dict with keys consistent, residual, rank, nullity, a_part (36,),
    null (36, nullity), or None-like fields if inconsistent.
    """
    C, rhs = coupled_system(K, Y)
    u, sv, vt = svd(C, full_matrices=True)
    scale = sv[0] if sv[0] > 0 else 1.0
    rank = int(np.sum(sv > rank_tol * scale))
    coeff = u.T @ rhs
    residual = float(norm(coeff[rank:]))
    consistent = residual <= 1e-8 * (1.0 + float(norm(rhs)))
    coef = np.zeros(C.shape[1])
    if rank:
        coef[:rank] = coeff[:rank] / sv[:rank]
    a_part = vt.T @ coef
    null = vt[rank:].T  # 36 x nullity
    return {
        "consistent": consistent,
        "residual": residual,
        "rank": rank,
        "nullity": int(C.shape[1] - rank),
        "sv": sv,
        "a_part": a_part,
        "null": null,
        "rhs_norm": float(norm(rhs)),
    }


def _as_matrix(vec: np.ndarray) -> np.ndarray:
    return np.asarray(vec, dtype=float).reshape(N, N)


def family_objective(fam: dict, z: np.ndarray, which: str = "s") -> tuple[float, np.ndarray]:
    """s(A(z)) or s(A)-k(A), plus gradient in z. which in {'s','gap'}."""
    A = _as_matrix(fam["a_part"] + fam["null"] @ np.asarray(z, dtype=float))
    if which == "s":
        val, gA = norm_grad_A(A, True)
        return val, gA.reshape(-1) @ fam["null"]
    sv, gS = norm_grad_A(A, True)
    kv, gK = norm_grad_A(A, False)
    # Value is s-k. Negative means a counterexample on this family.
    return sv - kv, (gS - gK).reshape(-1) @ fam["null"]


def minimize_symmetric(fam: dict, starts: int = 1, rng: np.random.Generator | None = None):
    """Convex minimization of s(A(z)). Returns best s, z, A, grad_norm."""
    nullity = fam["nullity"]
    if nullity == 0:
        val, jac = family_objective(fam, np.zeros(0), "s")
        return {
            "s": val,
            "z": np.zeros(0),
            "A": _as_matrix(fam["a_part"]),
            "grad_norm": float(norm(jac)),
            "success": True,
        }

    rng = rng or np.random.default_rng(0)
    best = None
    seeds = [np.zeros(nullity)]
    for _ in range(max(0, starts - 1)):
        seeds.append(rng.normal(scale=0.3, size=nullity))

    def fun(z):
        val, jac = family_objective(fam, z, "s")
        return val, jac

    for z0 in seeds:
        res = scipy_minimize(
            fun,
            z0,
            jac=True,
            method="L-BFGS-B",
            options={"maxiter": 80, "ftol": 1e-14, "gtol": 1e-8, "maxls": 20},
        )
        if best is None or res.fun < best["s"]:
            best = {
                "s": float(res.fun),
                "z": res.x.copy(),
                "A": _as_matrix(fam["a_part"] + fam["null"] @ res.x),
                "grad_norm": float(norm(res.jac)) if res.jac is not None else np.nan,
                "success": bool(res.success),
                "nit": int(res.nit),
                "nfev": int(res.nfev),
            }
    return best


def subdifferential_certificate(fam: dict, z: np.ndarray, gap_tol: float = 1e-6):
    """Minimum-norm convex combination of active symmetric singular-vector gradients.

    For the convex objective s(A(z)), a near-zero value is a numerical
    first-order certificate of global optimality when the active set is complete.
    The tolerance is absolute on singular values of the symmetric restriction.
    """

    A = _as_matrix(fam["a_part"] + fam["null"] @ np.asarray(z, dtype=float))
    basis = SYM[N]
    u, sv, vt = svd(op_matrix(A, basis), full_matrices=False)
    active = np.where(sv >= sv[0] - gap_tol)[0]
    grads = []
    for i in active:
        right = np.einsum("a,aij->ij", vt[i], basis)
        left = np.einsum("a,aij->ij", u[:, i], basis)
        gA = left @ right.T + left.T @ right
        grads.append(gA.reshape(-1) @ fam["null"])
    G = np.stack(grads, axis=0)  # m x nullity
    m = G.shape[0]
    if m == 1:
        return float(norm(G[0])), sv, active

    def f(lam):
        v = lam @ G
        return float(v @ v)

    def jac(lam):
        v = lam @ G
        return 2.0 * (G @ v)

    cons = {"type": "eq", "fun": lambda lam: np.sum(lam) - 1.0, "jac": lambda lam: np.ones(m)}
    res = scipy_minimize(
        f,
        np.full(m, 1.0 / m),
        jac=jac,
        bounds=[(0.0, 1.0)] * m,
        constraints=cons,
        method="SLSQP",
        options={"ftol": 1e-16, "maxiter": 200},
    )
    return float(np.sqrt(max(res.fun, 0.0))), sv, active


def maximize_gap_family(fam: dict, starts: int, rng: np.random.Generator):
    """Nonconvex local maximization of k(A)-s(A) over the affine family."""
    nullity = fam["nullity"]
    best_gap = -np.inf
    best = None
    for _ in range(starts):
        z0 = rng.normal(scale=0.4, size=nullity)

        def fun(z):
            val, jac = family_objective(fam, z, "gap")
            return val, jac

        res = scipy_minimize(
            fun,
            z0,
            jac=True,
            method="L-BFGS-B",
            options={"maxiter": 80, "ftol": 1e-14, "gtol": 1e-8},
        )
        gap = -float(res.fun)  # k-s
        if gap > best_gap:
            A = _as_matrix(fam["a_part"] + fam["null"] @ res.x)
            s, k = restricted_norms(A)
            best_gap = float(k - s)
            best = {"gap": best_gap, "s": s, "k": k, "z": res.x.copy(), "A": A}
    return best


def newton_retract(K: np.ndarray, y0: np.ndarray, niter: int = 12, tol: float = 1e-12):
    """Project skew coordinates y onto tr((YK)^j (Y^2-K^2))=0 for j=0,1,2.

    Returns (y, Y, success, moment_norm).
    """
    y = np.asarray(y0, dtype=float).copy()
    eye = np.eye(3)
    for _ in range(niter):
        Y = skew_from_coords(y)
        m = moments(K, Y, 3)
        mn = float(norm(m))
        if mn < tol:
            return y, Y, True, mn
        J = np.empty((3, 15))
        # Analytic-free but cheap one-sided differences. Central is unnecessary.
        eps = 1e-8
        for a in range(15):
            y[a] += eps
            Ya = skew_from_coords(y)
            J[:, a] = (moments(K, Ya, 3) - m) / eps
            y[a] -= eps
        dy, _, rank, _ = lstsq(J, -m, rcond=1e-12)
        if rank < 3:
            # Damped least-squares step if the moment Jacobian drops rank.
            dy = lstsq(J.T @ J + 1e-8 * eye, J.T @ (-m), rcond=None)[0]
        y = y + dy
    Y = skew_from_coords(y)
    mn = float(norm(moments(K, Y, 3)))
    return y, Y, mn < 1e-8, mn


def singular_values_skew(K: np.ndarray) -> np.ndarray:
    return svd(K, compute_uv=False)


def eval_pair(K: np.ndarray, Y: np.ndarray, rng: np.random.Generator, gap_starts: int = 0, certify: bool = True):
    """Exact elimination for one pair. phi = min s(A) on the coupled affine family.

    A positive reported gap means k>s at a matrix in the family (counterexample
    candidate). phi < 1 is the sufficient convex certificate.
    """
    fam = factor_family(K, Y)
    out = {
        "consistent": fam["consistent"],
        "residual": fam["residual"],
        "rank": fam["rank"],
        "nullity": fam["nullity"],
        "sigma_min_K": float(singular_values_skew(K)[-1]),
        "sigma_min_Y": float(singular_values_skew(Y)[-1]),
        "fro_K": float(norm(K)),
        "fro_Y": float(norm(Y)),
    }
    if not fam["consistent"] or fam["nullity"] < 0:
        out["phi"] = np.inf
        return out, None
    opt = minimize_symmetric(fam, starts=1, rng=rng)
    A = opt["A"]
    s_chk, k_chk = restricted_norms(A)
    # Rebuild equations to measure true coupled residual.
    r1 = A @ K + K @ A.T - Y
    r2 = A.T @ Y + Y @ A - K
    out.update(
        {
            "phi": float(s_chk),
            "k_at_phi": float(k_chk),
            "gap_at_phi": float(k_chk - s_chk),
            "opt_grad_norm": opt["grad_norm"],
            "coupled_resid": float(np.sqrt(norm(r1) ** 2 + norm(r2) ** 2)),
            "A": A,
            "z": opt["z"],
            "nit": opt.get("nit"),
        }
    )
    if certify:
        cert_norm, spectrum, active = subdifferential_certificate(fam, opt["z"])
        out["cert_subgrad_norm"] = float(cert_norm)
        out["active_multiplicity"] = int(len(active))
        out["spectrum_s_top"] = float(spectrum[0])
    if gap_starts:
        gap_best = maximize_gap_family(fam, gap_starts, rng)
        out["gap_max"] = gap_best
    return out, fam


def random_canonical_K(rng: np.random.Generator, mode: str = "interior") -> np.ndarray:
    if mode == "interior":
        w = rng.uniform(0.25, 1.5, size=3)
    elif mode == "boundary":
        w = np.array(
            [
                rng.uniform(0.6, 1.5),
                rng.uniform(0.25, 1.0),
                10 ** rng.uniform(-4.0, -1.2),
            ]
        )
    elif mode == "equal":
        w = np.ones(3) + rng.normal(scale=0.08, size=3)
        w = np.clip(w, 0.05, None)
    elif mode == "calibration":
        w = np.array([1.0, 2.0, 3.0]) * (1.0 + rng.normal(scale=0.05, size=3))
        w = np.clip(w, 0.05, None)
    else:
        raise ValueError(mode)
    K = canon(w)
    return K / norm(K)


def sample_consistent_pair(rng: np.random.Generator, mode: str = "interior", tries: int = 8):
    """Return (K, Y, info) on the moment variety, or (None, None, info)."""
    if mode == "svd":
        A = rng.normal(size=(N, N))
        basis = SKEW[N]
        u, sv, vt = svd(op_matrix(A, basis), full_matrices=False)
        # Prefer well-conditioned witnesses with large singular value.
        scores = []
        pack = []
        for i in range(len(sv)):
            K = np.einsum("a,aij->ij", vt[i], basis)
            Y = np.einsum("a,aij->ij", u[:, i], basis)
            sk = float(svd(K, compute_uv=False)[-1])
            scores.append(sk * sv[i])
            pack.append((K, Y, sk, float(sv[i])))
        order = np.argsort(scores)[::-1]
        for i in order[:4]:
            K, Y, sk, sig = pack[i]
            if sk > 0.02 and sig > 1e-8:
                return K, Y, {"mode": mode, "sigma_min_K": sk, "op_sigma": sig}
        K, Y, sk, sig = pack[int(order[0])]
        return K, Y, {"mode": mode, "sigma_min_K": sk, "op_sigma": sig, "weak": True}

    for _ in range(tries):
        K = random_canonical_K(rng, "interior" if mode == "svd" else mode if mode != "perturb" else "calibration")
        if mode == "perturb":
            y = skew_coords(K) + rng.normal(scale=rng.uniform(0.02, 0.4), size=15)
        else:
            y = rng.normal(size=15)
        y, Y, ok, mn = newton_retract(K, y)
        if ok and float(svd(Y, compute_uv=False)[-1]) > 1e-3:
            return K, Y, {"mode": mode, "moment_norm": mn, "sigma_min_Y": float(svd(Y, compute_uv=False)[-1])}
    return None, None, {"mode": mode, "failed": True}


def relative_gap(k: float, s: float) -> float:
    return float((k - s) / max(s, k, 1e-15))


# Known Kressner–Vandereycken integer counterexample (arXiv:2608.20875, Theorem 2).
A7 = np.array(
    [
        [0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0],
        [6, -5, -13, 0, 0, 0, 0],
        [-14, -18, 0, 0, 0, 0, 0],
        [12, -12, 11, 0, 0, 0, 0],
        [0, 0, 0, -6, 0, -14, 0],
        [0, 0, 0, 6, -18, 0, 0],
    ],
    dtype=float,
)
K7 = np.array(
    [
        [0, 4, -9, 41, 71, 4, 6],
        [-4, 0, -11, -59, 105, -12, 3],
        [9, 11, 0, 59, -10, 36, -8],
        [-41, 59, -59, 0, 9, 0, 2],
        [-71, -105, 10, -9, 0, -15, 0],
        [-4, 12, -36, 0, 15, 0, 4],
        [-6, -3, 8, -2, 0, -4, 0],
    ],
    dtype=float,
)


def project_diag_skew(A: np.ndarray) -> np.ndarray:
    """Orthogonal projection onto diagonal-plus-skew matrices."""
    return np.diag(np.diag(A)) + 0.5 * (A - A.T)


def reduce_symmetric_part(A: np.ndarray) -> np.ndarray:
    _, Q = np.linalg.eigh(0.5 * (A + A.T))
    return Q.T @ A @ Q
