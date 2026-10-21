"""Local minimization of exact phi starting from the best penalty pair.

Finite-difference L-BFGS on the 18-parameter retraction (canonical weights
plus Newton-retracted skew Y). Writes every improvement.
"""
from __future__ import annotations

import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

import lyap as L
from exp_outer import evaluate, init_theta

OUT = Path(__file__).resolve().parent / "results" / "long" / "polish"
OUT.mkdir(parents=True, exist_ok=True)


def main():
    rng = np.random.default_rng(99)
    start = time.time()
    root = Path(__file__).resolve().parent / "results" / "long" / "penalty0"
    K0 = np.load(root / "best_K.npy")
    Y0 = np.load(root / "best_Y.npy")
    weights = np.array([K0[0, 1], K0[2, 3], K0[4, 5]], dtype=float)
    theta0 = np.zeros(18)
    theta0[:3] = np.log(np.abs(weights))
    theta0[3:] = L.skew_coords(Y0)
    base = evaluate(theta0, rng, mu=0.0, certify=False)
    print(json.dumps({"event": "start", "phi": base.get("phi"), "gap": base.get("gap"), "smin": [base.get("sigma_min_K"), base.get("sigma_min_Y")]}), flush=True)
    best = {"phi": base.get("phi", np.inf), "theta": theta0}
    if base.get("ok"):
        np.save(OUT / "best_A.npy", base["A"])
        np.save(OUT / "best_K.npy", base["K"])
        np.save(OUT / "best_Y.npy", base["Y"])

    def run_from(theta_init, tag, maxiter):
        nonlocal best
        evals = {"n": 0}

        def fun(theta):
            nonlocal best
            evals["n"] += 1
            rec = evaluate(theta, rng, mu=0.0, certify=False)
            if rec.get("ok") and rec["phi"] < best["phi"]:
                best = {"phi": rec["phi"], "gap": rec.get("gap"), "theta": theta.copy(),
                        "sminK": rec["sigma_min_K"], "sminY": rec["sigma_min_Y"], "tag": tag}
                np.save(OUT / "best_A.npy", rec["A"])
                np.save(OUT / "best_K.npy", rec["K"])
                np.save(OUT / "best_Y.npy", rec["Y"])
                np.save(OUT / "best_theta.npy", theta)
                (OUT / "best.json").write_text(json.dumps({k: best[k] for k in best if k != "theta"}, indent=2))
                print(json.dumps({"event": "improve", "tag": tag, "phi": rec["phi"], "gap": rec.get("gap"), "smin": [rec["sigma_min_K"], rec["sigma_min_Y"]], "evals": evals["n"]}), flush=True)
            return rec["value"] if np.isfinite(rec["value"]) else 1e3

        res = minimize(fun, theta_init, method="L-BFGS-B", options={"maxiter": maxiter, "ftol": 1e-14, "eps": 1e-4})
        rec = evaluate(res.x, rng, mu=0.0, certify=True)
        summary = {
            "tag": tag,
            "nit": int(res.nit),
            "nfev": int(res.nfev),
            "phi": rec.get("phi"),
            "gap": rec.get("gap"),
            "success": bool(res.success),
            "smin": [rec.get("sigma_min_K"), rec.get("sigma_min_Y")],
            "cert": rec.get("coupled_resid"),
            "elapsed": time.time() - start,
        }
        print(json.dumps({"event": "done", **summary}), flush=True)
        return summary

    summaries = []
    summaries.append(run_from(theta0, "near_miss", 25))
    for i in range(6):
        if time.time() - start > 1500:
            break
        th = theta0 + rng.normal(scale=0.05 * (i + 1), size=theta0.shape)
        summaries.append(run_from(th, f"perturb_{i}", 18))
    for i in range(4):
        if time.time() - start > 1500:
            break
        summaries.append(run_from(init_theta(rng, i), f"fresh_{i}", 15))
    (OUT / "summary.json").write_text(json.dumps({"best_phi": best["phi"], "runs": summaries}, indent=2))
    print(json.dumps({"event": "finished", "best_phi": best["phi"]}), flush=True)


if __name__ == "__main__":
    main()
