"""JAX multistart search for a dimension-6 Lyapunov counterexample.

Two families:

* penalty: minimize s(A) on the H-parameterization A=(H+Y/2) K^{-1},
  with a quadratic penalty on the second coupled equation and a log-det
  barrier that keeps the skew witnesses invertible.
* gap: Adam on the Frobenius sphere for k(A)-s(A), optional log-det
  barrier on the top skew witness (dimension 6 only).

Checkpoints are written next to --out. This is a numerical search, not a proof.
"""
from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")
os.environ.setdefault("VECLIB_MAXIMUM_THREADS", "1")
os.environ.setdefault("XLA_FLAGS", "--xla_cpu_multi_thread_eigen=false")

import numpy as np

# Thread caps must be set before JAX initializes XLA.
import jax

jax.config.update("jax_enable_x64", True)
jax.config.update("jax_platforms", "cpu")
import jax.numpy as jnp
from jax import lax

import lyap as L


def _basis_jnp(symmetric: bool, n: int) -> jnp.ndarray:
    src = L.SYM[n] if symmetric else L.SKEW[n]
    return jnp.asarray(src)


def canon_from_raw(raw: jnp.ndarray) -> jnp.ndarray:
    w = jnp.exp(raw - jnp.max(raw))
    w = w / jnp.linalg.norm(w)
    K = jnp.zeros((6, 6))
    blocks = []
    for t in range(3):
        block = w[t] * jnp.array([[0.0, 1.0], [-1.0, 0.0]])
        blocks.append(block)
    K = K.at[0:2, 0:2].set(blocks[0])
    K = K.at[2:4, 2:4].set(blocks[1])
    K = K.at[4:6, 4:6].set(blocks[2])
    K = K / jnp.linalg.norm(K)
    return K, w


def skew_from_raw(raw: jnp.ndarray, basis: jnp.ndarray) -> jnp.ndarray:
    Y = jnp.einsum("a,aij->ij", raw, basis)
    return Y / jnp.linalg.norm(Y)


def sym_from_raw(raw: jnp.ndarray, basis: jnp.ndarray) -> jnp.ndarray:
    return jnp.einsum("a,aij->ij", raw, basis)


def op_singular_values(A: jnp.ndarray, basis: jnp.ndarray) -> jnp.ndarray:
    images = jnp.einsum("ij,mjk->mik", A, basis) + jnp.einsum("mij,jk->mik", basis, A.T)
    B = jnp.einsum("mij,kij->mk", basis, images)
    return jnp.linalg.svd(B, compute_uv=False)


def op_top(A: jnp.ndarray, basis: jnp.ndarray):
    images = jnp.einsum("ij,mjk->mik", A, basis) + jnp.einsum("mij,jk->mik", basis, A.T)
    B = jnp.einsum("mij,kij->mk", basis, images)
    u, s, vt = jnp.linalg.svd(B, full_matrices=False)
    return s[0], u[:, 0], vt[0], s


def penalty_pack(theta, sym_b, skew_b):
    K, w = canon_from_raw(theta[:3])
    Y = skew_from_raw(theta[3:18], skew_b)
    H = sym_from_raw(theta[18:], sym_b)
    A = (H + 0.5 * Y) @ jnp.linalg.inv(K)
    R = A.T @ Y + Y @ A - K
    return A, K, Y, w, R


def make_penalty_loss(sym_b, skew_b):
    def loss(theta, rho, mu):
        A, K, Y, w, R = penalty_pack(theta, sym_b, skew_b)
        res = jnp.sum(R * R)
        sig = op_singular_values(A, sym_b)[0]
        _, logdet = jnp.linalg.slogdet(Y)
        pen = -jnp.sum(jnp.log(w)) - jnp.clip(logdet, -40.0, 40.0)
        # k lower bound is 1 only when res=0 and ||K||=||Y||=1, which the
        # parameterization enforces for the norms. sig<1 with res~0 is a hit.
        total = sig + rho * res + mu * pen
        return total, (sig, res, pen)

    return loss


def make_gap_loss(n, sym_b, skew_b, barrier: bool):
    def loss(theta, mu):
        A = theta.reshape(n, n)
        A = A / jnp.linalg.norm(A)
        s = op_singular_values(A, sym_b)[0]
        if barrier:
            kval, u, vt, _ = op_top(A, skew_b)
            K = jnp.einsum("a,aij->ij", vt, skew_b)
            _, logdet = jnp.linalg.slogdet(K)
            pen = -jnp.clip(logdet, -40.0, 40.0)
            # Maximize k-s-mu*pen, i.e. minimize s-k + mu*pen.
            # slogdet is -inf on singular K, so the barrier repels the rank-4 ridge.
            return s - kval + mu * pen, (s, kval, pen)
        kval = op_singular_values(A, skew_b)[0]
        return s - kval, (s, kval, 0.0)

    return loss


def adam_scan(loss_fn, nsteps: int):
    """loss_fn(theta, hyper) -> (scalar, aux). hyper is a tuple of scalars."""

    def scan_body(state, _):
        theta, m, v, t, hyper, lr = state
        (val, aux), g = jax.value_and_grad(loss_fn, has_aux=True)(theta, *hyper)
        g = jnp.where(jnp.isfinite(g), g, 0.0)
        t = t + 1
        m = 0.9 * m + 0.1 * g
        v = 0.999 * v + 0.001 * (g * g)
        mhat = m / (1 - 0.9**t)
        vhat = v / (1 - 0.999**t)
        theta = theta - lr * mhat / (jnp.sqrt(vhat) + 1e-8)
        return (theta, m, v, t, hyper, lr), (val, aux)

    def run(theta, hyper, lr):
        m = jnp.zeros_like(theta)
        v = jnp.zeros_like(theta)
        state = (theta, m, v, jnp.array(0, dtype=jnp.int32), hyper, lr)
        # Rebuild hyper into the state each call; lax.scan captures it.
        def body(st, _):
            return scan_body(st, None)

        state, aux = lax.scan(body, state, None, length=nsteps)
        return state[0], aux

    return jax.jit(run)


def numpy_penalty_metrics(theta: np.ndarray) -> dict:
    raw = theta[:3]
    w = np.exp(raw - raw.max())
    w = w / np.linalg.norm(w)
    K = L.canon(w)
    K = K / np.linalg.norm(K)
    Y = L.skew_from_coords(theta[3:18])
    Y = Y / np.linalg.norm(Y)
    H = L.sym_from_coords(theta[18:])
    A = (H + 0.5 * Y) @ np.linalg.inv(K)
    R = A.T @ Y + Y @ A - K
    s, k = L.restricted_norms(A)
    return {
        "s": s,
        "k": k,
        "gap": k - s,
        "rel_gap": L.relative_gap(k, s),
        "residual": float(np.linalg.norm(R)),
        "sigma_min_K": float(np.linalg.svd(K, compute_uv=False)[-1]),
        "sigma_min_Y": float(np.linalg.svd(Y, compute_uv=False)[-1]),
        "weights": w.tolist(),
        "A": A,
        "K": K,
        "Y": Y,
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--mode", choices=["penalty", "gap", "gap7"], required=True)
    p.add_argument("--seconds", type=float, default=600)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--mu", type=float, default=0.01)
    p.add_argument("--rho", type=float, default=20.0)
    p.add_argument("--lr", type=float, default=0.02)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    n = 7 if args.mode == "gap7" else 6
    sym_b = _basis_jnp(True, n if args.mode != "penalty" else 6)
    skew_b = _basis_jnp(False, n if args.mode != "penalty" else 6)
    if args.mode == "penalty":
        sym_b = _basis_jnp(True, 6)
        skew_b = _basis_jnp(False, 6)
        loss = make_penalty_loss(sym_b, skew_b)

        def loss_scan(theta, rho, mu):
            return loss(theta, rho, mu)

        runner = adam_scan(loss_scan, 200)
        dim = 39
    else:
        loss = make_gap_loss(n, sym_b, skew_b, barrier=(args.mode == "gap"))

        def loss_scan(theta, mu):
            return loss(theta, mu)

        runner = adam_scan(loss_scan, 200)
        dim = n * n

    # Compile on a nonsingular point. The zero vector makes Y or A vanish.
    compile_theta = jnp.asarray(np.linspace(0.2, 0.5, dim))
    if args.mode == "penalty":
        runner(compile_theta, (jnp.asarray(args.rho), jnp.asarray(args.mu)), jnp.asarray(args.lr))
    else:
        runner(compile_theta, (jnp.asarray(args.mu),), jnp.asarray(args.lr))

    start = time.time()
    starts = 0
    best = {
        "score": np.inf,
        "rel_gap": -np.inf,
        "feasible_phi": np.inf,
    }
    history = []
    log_path = args.out / "log.jsonl"

    def consider_penalty(theta, tag):
        met = numpy_penalty_metrics(np.asarray(theta))
        feasible = met["residual"] < 1e-7
        score = met["s"] + (0.0 if feasible else 1e4 * met["residual"])
        rec = {
            "tag": tag,
            "s": met["s"],
            "k": met["k"],
            "gap": met["gap"],
            "rel_gap": met["rel_gap"],
            "residual": met["residual"],
            "sigma_min_K": met["sigma_min_K"],
            "sigma_min_Y": met["sigma_min_Y"],
            "weights": met["weights"],
            "feasible": feasible,
            "score": score,
            "elapsed": time.time() - start,
        }
        improved = False
        if feasible and met["s"] < best["feasible_phi"]:
            best["feasible_phi"] = met["s"]
            improved = True
        if met["rel_gap"] > best["rel_gap"] and met["residual"] < 1e-4:
            best["rel_gap"] = met["rel_gap"]
            improved = True
        if score < best["score"]:
            best["score"] = score
            improved = True
        # Exact projection onto the coupled variety when the penalty is close.
        if met["residual"] < 1e-4 and met["s"] < 1.05:
            try:
                exact, _fam = L.eval_pair(met["K"], met["Y"], np.random.default_rng(0), certify=False)
            except np.linalg.LinAlgError:
                exact = None
            if exact and exact.get("consistent") and np.isfinite(exact.get("phi", np.inf)):
                rec["exact_phi"] = exact["phi"]
                rec["exact_gap"] = exact["gap_at_phi"]
                rec["exact_coupled_resid"] = exact["coupled_resid"]
                if exact["phi"] < best["feasible_phi"]:
                    best["feasible_phi"] = exact["phi"]
                    improved = True
                if exact["gap_at_phi"] > best["rel_gap"]:
                    best["rel_gap"] = exact["gap_at_phi"]
                    improved = True
        if improved:
            history.append(rec)
            np.save(args.out / "best_A.npy", met["A"])
            np.save(args.out / "best_K.npy", met["K"])
            np.save(args.out / "best_Y.npy", met["Y"])
            np.save(args.out / "best_theta.npy", np.asarray(theta))
            (args.out / "best.json").write_text(json.dumps({**rec, "theta_file": "best_theta.npy"}, indent=2))
        return rec

    def consider_gap(theta):
        A = np.asarray(theta).reshape(n, n)
        A = A / np.linalg.norm(A)
        s, k = L.restricted_norms(A)
        rel = L.relative_gap(k, s)
        rec = {"s": s, "k": k, "gap": k - s, "rel_gap": rel, "elapsed": time.time() - start, "starts": starts}
        if rel > best["rel_gap"]:
            best["rel_gap"] = rel
            np.save(args.out / "best_A.npy", A)
            (args.out / "best.json").write_text(json.dumps(rec, indent=2))
            history.append(rec)
        return rec

    while time.time() - start < args.seconds:
        starts += 1
        if args.mode == "penalty":
            kind = starts % 5
            if kind == 0:
                theta = np.zeros(dim)
                theta[:3] = np.log(np.array([1.0, 2.0, 3.0]))
                K0 = L.canon([1.0, 2.0, 3.0])
                K0 /= np.linalg.norm(K0)
                theta[3:18] = L.skew_coords(K0)
                theta += rng.normal(scale=0.15, size=dim)
            elif kind == 1:
                theta = np.zeros(dim)
                theta[:3] = np.log(np.array([1.0, 1.0, 1.0]))
                K0 = L.canon([1.0, 1.0, 1.0])
                K0 /= np.linalg.norm(K0)
                theta[3:18] = L.skew_coords(K0) + rng.normal(scale=0.3, size=15)
                theta[18:] = rng.normal(scale=0.2, size=21)
            elif kind == 2:
                theta = rng.normal(scale=0.7, size=dim)
            elif kind == 3:
                theta = rng.normal(scale=0.25, size=dim)
                theta[:3] = np.log(np.array([1.0, 0.7, 0.05]))
            else:
                theta = rng.normal(scale=1.0, size=dim)
            theta = jnp.asarray(theta)
            # rho multiplies ||R||_F^2. Values below ~1e4 do not pin the
            # second coupled equation; the last stage targets ||R|| ~ 1e-6.
            for rho, lr, mu in (
                (max(args.rho, 1.0), args.lr, args.mu),
                (max(args.rho, 1.0) * 100.0, args.lr * 0.25, args.mu),
                (max(args.rho, 1.0) * 10000.0, args.lr * 0.05, args.mu * 0.3),
            ):
                if time.time() - start >= args.seconds:
                    break
                theta, _ = runner(
                    theta,
                    (jnp.asarray(float(rho)), jnp.asarray(float(mu))),
                    jnp.asarray(float(lr)),
                )
            rec = consider_penalty(theta, "penalty")
        else:
            A0 = rng.normal(size=(n, n))
            if args.mode == "gap7" and starts % 4 == 1:
                A0 = L.A7 + rng.normal(scale=0.05, size=A0.shape)
            theta = jnp.asarray(A0.reshape(-1))
            lr = 0.02 if args.mode == "gap7" else args.lr
            for lr_now in (lr, lr * 0.4):
                if time.time() - start >= args.seconds:
                    break
                theta, _ = runner(theta, (jnp.asarray(args.mu),), jnp.asarray(lr_now))
                theta = theta / jnp.linalg.norm(theta)
            rec = consider_gap(theta)
        hit = rec.get("rel_gap", -1) > 1e-6 or (rec.get("feasible") and rec.get("s", 2) < 0.999999)
        hit = hit or rec.get("exact_phi", 2) < 0.999999 or rec.get("exact_gap", -1) > 1e-6
        if starts % 25 == 0 or hit:
            line = {"starts": starts, "elapsed": round(time.time() - start, 1), **{k: rec[k] for k in rec if k != "weights"}}
            if "weights" in rec:
                line["weights"] = rec["weights"]
            line["best_rel_gap"] = best["rel_gap"]
            line["best_feasible_phi"] = best.get("feasible_phi")
            with log_path.open("a") as fh:
                fh.write(json.dumps(line) + "\n")
            print(json.dumps(line), flush=True)

    summary = {
        "mode": args.mode,
        "seed": args.seed,
        "mu": args.mu,
        "rho": args.rho,
        "seconds": time.time() - start,
        "starts": starts,
        "best_rel_gap": best["rel_gap"],
        "best_feasible_phi": best.get("feasible_phi"),
        "best_score": best.get("score"),
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
