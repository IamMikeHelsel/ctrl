"""Continuation from the dimension-7 counterexample down toward dimension 6.

The published matrix has a fragile positive gap: scaling its last row by 0.9
already makes k<s. This script reoptimizes the blocks along the homotopy

    A(t) = [[B, t u], [t v^T, t w]]

and also runs plain Adam at n=7 (sanity: the optimizer can see a positive gap)
and at n=6 from the best compressions.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
from numpy.linalg import norm, qr, svd

import lyap as L


def gap_grad(A: np.ndarray):
    s, gs = L.norm_grad_A(A, True)
    k, gk = L.norm_grad_A(A, False)
    return k - s, gk - gs, s, k


def adam_sphere(A0: np.ndarray, steps: int, lr0: float = 0.02, rng=None):
    A = A0 / norm(A0)
    m = np.zeros_like(A)
    v = np.zeros_like(A)
    best = -np.inf
    best_A = A.copy()
    history = []
    for it in range(1, steps + 1):
        gap, g, s, k = gap_grad(A)
        if gap > best:
            best = gap
            best_A = A.copy()
            history.append({"it": it, "gap": gap, "rel": L.relative_gap(k, s), "s": s, "k": k})
        g = g - np.sum(g * A) * A
        m = 0.9 * m + 0.1 * g
        v = 0.999 * v + 0.001 * g * g
        lr = lr0 * (1.0 - 0.85 * ((it - 1) % 800) / 800.0) ** 2
        if it > 800:
            lr *= 0.3
        A = A + lr * (m / (1 - 0.9**it)) / (np.sqrt(v / (1 - 0.999**it)) + 1e-8)
        A /= norm(A)
    s, k = L.restricted_norms(best_A)
    return best_A, {"gap": float(k - s), "s": s, "k": k, "rel": L.relative_gap(k, s), "history_len": len(history), "trace": history[:12]}


def assemble(B, u, v, w, t):
    A = np.zeros((7, 7))
    A[:6, :6] = B
    A[:6, 6] = t * u
    A[6, :6] = t * v
    A[6, 6] = t * w
    return A


def renorm_pack(B, u, v, w):
    nrm = np.sqrt(norm(B) ** 2 + norm(u) ** 2 + norm(v) ** 2 + float(w) ** 2)
    if nrm < 1e-14:
        return B, u, v, w
    return B / nrm, u / nrm, v / nrm, float(w) / nrm


def pack_grad(B, u, v, w, t):
    """Gradient of the spherical gap w.r.t. a unit parameter pack at fixed t.

    The pack (B,u,v,w) is kept on the unit sphere, so t->0 really decouples
    the last coordinate instead of letting u,v blow up like 1/t.
    """
    B, u, v, w = renorm_pack(B, u, v, w)
    M = assemble(B, u, v, w, t)
    nrm = norm(M)
    if nrm < 1e-14:
        return np.zeros_like(B), np.zeros_like(u), np.zeros_like(v), 0.0, -1.0, M
    A = M / nrm
    gap, G, s, k = gap_grad(A)
    GM = (G - np.sum(G * A) * A) / nrm
    gB = GM[:6, :6]
    gu = t * GM[:6, 6]
    gv = t * GM[6, :6]
    gw = float(t * GM[6, 6])
    # Tangent projection on the parameter sphere.
    inner = float(np.sum(gB * B) + np.dot(gu, u) + np.dot(gv, v) + gw * w)
    gB = gB - inner * B
    gu = gu - inner * u
    gv = gv - inner * v
    gw = gw - inner * w
    return gB, gu, gv, gw, gap, A


def continue_t(B, u, v, w, steps_each=250, lr=0.03):
    path = []
    ts = [1.0, 0.85, 0.7, 0.55, 0.4, 0.3, 0.2, 0.12, 0.06, 0.02, 0.0]
    mB = np.zeros_like(B)
    mu = np.zeros_like(u)
    mv = np.zeros_like(v)
    mw = 0.0
    vb = np.zeros_like(B)
    vu = np.zeros_like(u)
    vv = np.zeros_like(v)
    vw = 0.0
    for t in ts:
        best_gap = -np.inf
        best_pack = None
        for it in range(1, steps_each + 1):
            gB, gu, gv, gw, gap, A = pack_grad(B, u, v, w, t)
            if gap > best_gap:
                best_gap = gap
                best_pack = (B.copy(), u.copy(), v.copy(), w, A.copy())
            mB = 0.9 * mB + 0.1 * gB
            mu = 0.9 * mu + 0.1 * gu
            mv = 0.9 * mv + 0.1 * gv
            mw = 0.9 * mw + 0.1 * gw
            vb = 0.999 * vb + 0.001 * gB * gB
            vu = 0.999 * vu + 0.001 * gu * gu
            vv = 0.999 * vv + 0.001 * gv * gv
            vw = 0.999 * vw + 0.001 * gw * gw
            rate = lr * (0.5 if it > steps_each // 2 else 1.0)
            B = B + rate * (mB / (1 - 0.9**it)) / (np.sqrt(vb / (1 - 0.999**it)) + 1e-8)
            u = u + rate * (mu / (1 - 0.9**it)) / (np.sqrt(vu / (1 - 0.999**it)) + 1e-8)
            v = v + rate * (mv / (1 - 0.9**it)) / (np.sqrt(vv / (1 - 0.999**it)) + 1e-8)
            w = w + rate * (mw / (1 - 0.9**it)) / (np.sqrt(vw / (1 - 0.999**it)) + 1e-8)
            B, u, v, w = renorm_pack(B, u, v, w)
        B, u, v, w, A = best_pack
        B, u, v, w = renorm_pack(B, u, v, w)
        s6, k6 = L.restricted_norms(B)
        s7, k7 = L.restricted_norms(A)
        # Witness conditioning of the 7x7 optimizer matrix and of B.
        _, K, Y = L.top_singular_pair(A, False)
        rec = {
            "t": t,
            "gap7": float(k7 - s7),
            "rel7": L.relative_gap(k7, s7),
            "s7": s7,
            "k7": k7,
            "gap6": float(k6 - s6),
            "rel6": L.relative_gap(k6, s6),
            "s6": s6,
            "k6": k6,
            "fro_coupling": float(np.sqrt(norm(u) ** 2 + norm(v) ** 2 + w**2)),
            "smin_witness7": float(svd(K, compute_uv=False)[-1]),
        }
        path.append(rec)
        print(json.dumps(rec), flush=True)
    return path, B, u, v, w


def initial_split(A, drop: int):
    perm = [i for i in range(7) if i != drop] + [drop]
    P = A[np.ix_(perm, perm)]
    return P[:6, :6].copy(), P[:6, 6].copy(), P[6, :6].copy(), float(P[6, 6])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=900)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--seed", type=int, default=11)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    deadline = time.time() + args.seconds
    report = {"n7_runs": [], "deflations": [], "n6_from_compression": []}
    # Fat n=7 matrices already found by the JAX sphere search.
    for extra in (Path(__file__).resolve().parent / "results").glob("*/best_A.npy"):
        try:
            trial = np.load(extra)
        except Exception:
            continue
        if trial.shape == (7, 7):
            dest = args.out / f"n7_A_pre_{extra.parent.name}.npy"
            if not dest.exists():
                np.save(dest, trial)
                print(json.dumps({"preloaded": str(extra)}), flush=True)

    # Sanity: Adam must recover a positive gap in dimension 7.
    print("n7 adam", flush=True)
    for i in range(6):
        if time.time() > deadline:
            break
        if i == 0:
            A0 = L.A7.copy()
        else:
            A0 = rng.normal(size=(7, 7))
        A, info = adam_sphere(A0, steps=500, lr0=0.03, rng=rng)
        info["start"] = i
        _, K, _ = L.top_singular_pair(A, False)
        info["smin_witness"] = float(svd(K, compute_uv=False)[-1])
        report["n7_runs"].append(info)
        print(json.dumps(info), flush=True)
        if info["gap"] > 1e-4:
            np.save(args.out / f"n7_A_{i}.npy", A)

    # Deflate the published example along every coordinate, reoptimizing.
    print("deflate published", flush=True)
    for drop in range(7):
        if time.time() > deadline:
            break
        B, u, v, w = initial_split(L.A7, drop)
        print(json.dumps({"drop": drop, "phase": "start"}), flush=True)
        path, B, u, v, w = continue_t(B, u, v, w, steps_each=180, lr=0.04)
        report["deflations"].append({"source": "published", "drop": drop, "path": path})
        np.save(args.out / f"deflate_published_drop{drop}_B.npy", B)
        # Polish the resulting 6x6 directly.
        if time.time() > deadline:
            break
        A6, info6 = adam_sphere(B, steps=400, lr0=0.02)
        info6["from"] = f"published_drop_{drop}"
        report["n6_from_compression"].append(info6)
        print(json.dumps({"polish6": info6}), flush=True)
        if info6["gap"] > report.get("best_n6_gap", -np.inf):
            report["best_n6_gap"] = info6["gap"]
            np.save(args.out / "best_n6.npy", A6)

    # If a fatter n=7 example was found, deflate its best coordinate too.
    n7_files = sorted(args.out.glob("n7_A_*.npy"))
    for f in n7_files[:4]:
        if time.time() > deadline:
            break
        A = np.load(f)
        # Choose the coordinate whose deletion hurts the gap the least.
        best_drop = None
        best_g = -np.inf
        for drop in range(7):
            idx = [i for i in range(7) if i != drop]
            g = L.restricted_norms(A[np.ix_(idx, idx)])
            gap = g[1] - g[0]
            if gap > best_g:
                best_g = gap
                best_drop = drop
        B, u, v, w = initial_split(A, best_drop)
        print(json.dumps({"source": f.name, "drop": best_drop, "principal_gap": best_g}), flush=True)
        path, B, u, v, w = continue_t(B, u, v, w, steps_each=160, lr=0.04)
        report["deflations"].append({"source": f.name, "drop": best_drop, "path": path})
        A6, info6 = adam_sphere(B, steps=300, lr0=0.02)
        info6["from"] = f.name
        report["n6_from_compression"].append(info6)
        if info6["gap"] > report.get("best_n6_gap", -np.inf):
            report["best_n6_gap"] = info6["gap"]
            np.save(args.out / "best_n6.npy", A6)

    # Grassmann compression of published A7, then polish, a few random planes.
    print("grassmann polish", flush=True)
    for i in range(8):
        if time.time() > deadline:
            break
        if i < 7:
            idx = [j for j in range(7) if j != i]
            Q = np.eye(7)[:, idx]
        else:
            X = rng.normal(size=(7, 6))
            Q, _ = qr(X)
        M = Q.T @ L.A7 @ Q
        A6, info6 = adam_sphere(M, steps=350, lr0=0.02)
        info6["from"] = f"compress_{i}"
        report["n6_from_compression"].append({k: info6[k] for k in info6 if k != "trace"})
        print(json.dumps({"compress_polish": info6["from"], "gap": info6["gap"], "rel": info6["rel"]}), flush=True)

    def conv(o):
        if isinstance(o, (np.floating,)):
            return float(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, dict):
            return {k: conv(v) for k, v in o.items()}
        if isinstance(o, list):
            return [conv(v) for v in o]
        return o

    (args.out / "deflate.json").write_text(json.dumps(conv(report), indent=2))
    print(json.dumps({"best_n6_gap": report.get("best_n6_gap"), "n7": [r["gap"] for r in report["n7_runs"]]}), flush=True)


if __name__ == "__main__":
    main()
