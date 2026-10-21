"""Exact bilevel search: minimize phi(K,Y)=min s(A) on the coupled affine family.

K is gauge-fixed to canonical skew form. Y is retracted onto the three
moment conditions by Newton. The inner problem is convex (spectral norm of
an affine matrix pencil). A value phi<1, or a positive k-s on that family,
is a numerical counterexample candidate.

SPSA-Adam plus occasional L-BFGS polish. Checkpoints the Pareto front of
phi against witness conditioning.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import numpy as np
from numpy.linalg import norm

import lyap as L


def retract(theta: np.ndarray):
    raw = theta[:3]
    w = np.exp(raw - np.max(raw))
    w = w / norm(w)
    K = L.canon(w)
    K = K / norm(K)
    y, Y, ok, mn = L.newton_retract(K, theta[3:], niter=10, tol=1e-11)
    smin_y = float(np.linalg.svd(Y, compute_uv=False)[-1]) if ok else 0.0
    return K, Y, ok, mn, w, smin_y


def evaluate(theta: np.ndarray, rng, mu: float, certify: bool = False):
    K, Y, ok, mn, w, smin_y = retract(theta)
    smin_k = float(np.linalg.svd(K, compute_uv=False)[-1])
    if not ok:
        return {
            "ok": False,
            "value": 8.0 + 20.0 * mn,
            "phi": np.inf,
            "moment": mn,
            "sigma_min_K": smin_k,
            "sigma_min_Y": smin_y,
            "weights": w,
        }
    out, _fam = L.eval_pair(K, Y, rng, certify=certify)
    if not out.get("consistent") or not np.isfinite(out.get("phi", np.inf)):
        return {
            "ok": False,
            "value": 6.0 + float(out.get("residual", 1.0)),
            "phi": np.inf,
            "sigma_min_K": smin_k,
            "sigma_min_Y": out.get("sigma_min_Y", smin_y),
            "weights": w,
            "residual": out.get("residual"),
        }
    pen = -np.sum(np.log(np.clip(w, 1e-12, None))) - np.log(max(out["sigma_min_Y"], 1e-12))
    return {
        "ok": True,
        "value": float(out["phi"] + mu * pen),
        "phi": float(out["phi"]),
        "gap": float(out["gap_at_phi"]),
        "k": float(out["k_at_phi"]),
        "coupled_resid": float(out["coupled_resid"]),
        "sigma_min_K": float(out["sigma_min_K"]),
        "sigma_min_Y": float(out["sigma_min_Y"]),
        "weights": w.tolist(),
        "pen": float(pen),
        "A": out["A"],
        "K": K,
        "Y": Y,
    }


def bins_update(front: dict, rec: dict):
    if not rec.get("ok"):
        return
    key = float(min(rec["sigma_min_K"], rec["sigma_min_Y"]))
    # Geometric bins.
    edges = [0.3, 0.15, 0.08, 0.04, 0.02, 0.01, 0.0]
    label = "lt_0"
    for e in edges:
        if key >= e:
            label = f"ge_{e}"
            break
    cur = front.get(label)
    if cur is None or rec["phi"] < cur["phi"]:
        front[label] = {
            "phi": rec["phi"],
            "gap": rec.get("gap"),
            "sigma_min_K": rec["sigma_min_K"],
            "sigma_min_Y": rec["sigma_min_Y"],
            "weights": rec["weights"],
            "coupled_resid": rec.get("coupled_resid"),
        }


def spsa_step(theta, value_fn, rng, eps, lr, m, v, t):
    delta = rng.choice(np.array([-1.0, 1.0]), size=theta.shape)
    fp = value_fn(theta + eps * delta)
    fm = value_fn(theta - eps * delta)
    g = (fp - fm) / (2 * eps) * delta
    g = np.nan_to_num(g, nan=0.0, posinf=0.0, neginf=0.0)
    t += 1
    m = 0.9 * m + 0.1 * g
    v = 0.999 * v + 0.001 * g * g
    mhat = m / (1 - 0.9**t)
    vhat = v / (1 - 0.999**t)
    theta = theta - lr * mhat / (np.sqrt(vhat) + 1e-8)
    return theta, m, v, t, fp, fm


def init_theta(rng, kind: int) -> np.ndarray:
    theta = np.zeros(18)
    if kind == 0:
        theta[:3] = np.log([1.0, 2.0, 3.0])
        K = L.canon([1.0, 2.0, 3.0])
        K /= norm(K)
        theta[3:] = L.skew_coords(K)
        theta += rng.normal(scale=0.08, size=18)
    elif kind == 1:
        theta[:3] = np.log([1.0, 1.2, 1.5])
        theta[3:] = rng.normal(scale=0.6, size=15)
    elif kind == 2:
        theta[:3] = np.log([1.0, 0.8, 0.15])
        theta[3:] = rng.normal(scale=0.5, size=15)
    elif kind == 3:
        theta[:3] = rng.normal(size=3)
        K = L.random_canonical_K(rng, "equal")
        theta[3:] = L.skew_coords(K) + rng.normal(scale=0.2, size=15)
    else:
        theta[:3] = rng.normal(scale=0.5, size=3)
        theta[3:] = rng.normal(scale=0.8, size=15)
    return theta


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=600)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--mu", type=float, default=0.005)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    start = time.time()
    front: dict = {}
    best_phi = np.inf
    best_gap = -np.inf
    evals = 0
    starts = 0
    log_path = args.out / "log.jsonl"

    def value_only(theta):
        nonlocal evals
        evals += 1
        rec = evaluate(theta, rng, args.mu, certify=False)
        bins_update(front, rec)
        return rec

    while time.time() - start < args.seconds:
        starts += 1
        theta = init_theta(rng, starts % 5)
        m = np.zeros_like(theta)
        v = np.zeros_like(theta)
        t = 0
        lr = 0.04
        eps = 0.04
        last_rec = None
        for step in range(40):
            if time.time() - start >= args.seconds:
                break

            def vf(th, _lr_unused=None):
                return value_only(th)["value"]

            # Recompute the record at the current point every few steps.
            theta, m, v, t, fp, fm = spsa_step(theta, vf, rng, eps, lr, m, v, t)
            if step % 5 == 4:
                last_rec = value_only(theta)
                if last_rec.get("ok") and last_rec["phi"] < best_phi:
                    best_phi = last_rec["phi"]
                    np.save(args.out / "best_phi_A.npy", last_rec["A"])
                    np.save(args.out / "best_phi_K.npy", last_rec["K"])
                    np.save(args.out / "best_phi_Y.npy", last_rec["Y"])
                    np.save(args.out / "best_phi_theta.npy", theta)
                if last_rec.get("ok") and last_rec.get("gap", -1) > best_gap:
                    best_gap = last_rec["gap"]
                    np.save(args.out / "best_gap_A.npy", last_rec["A"])
                lr *= 0.92
                eps *= 0.92
        if last_rec is None:
            last_rec = value_only(theta)
        if starts % 2 == 0:
            line = {
                "starts": starts,
                "evals": evals,
                "elapsed": round(time.time() - start, 1),
                "best_phi": best_phi,
                "best_gap": best_gap,
                "front": front,
                "last_phi": last_rec.get("phi"),
                "last_ok": last_rec.get("ok"),
                "last_smin": [last_rec.get("sigma_min_K"), last_rec.get("sigma_min_Y")],
            }
            with log_path.open("a") as fh:
                fh.write(json.dumps(line) + "\n")
            print(json.dumps({"starts": starts, "evals": evals, "best_phi": best_phi, "best_gap": best_gap, "elapsed": line["elapsed"], "front_phi": {k: v["phi"] for k, v in front.items()}}), flush=True)

    summary = {
        "seed": args.seed,
        "mu": args.mu,
        "seconds": time.time() - start,
        "starts": starts,
        "evals": evals,
        "best_phi": best_phi,
        "best_gap": best_gap,
        "front": front,
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
